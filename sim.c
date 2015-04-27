#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdarg.h>
#include <stdbool.h>
#include <assert.h>
#include <math.h>
#include <string.h>
#include <errno.h>
#include "debug.h"

/* Quasi binary literal. Ex. B(11001) for decimal 25 */

#define PP_HEX2BIN(b)                                                   \
  (((b & 1 <<  0) >>  0) + ((b & 1 <<  3) >>  2) + ((b & 1 <<  6) >>  4) + \
   ((b & 1 <<  9) >>  6) + ((b & 1 << 12) >>  8) + ((b & 1 << 15) >> 10) + \
   ((b & 1 << 18) >> 12) + ((b & 1 << 21) >> 14))
#define B(x) PP_HEX2BIN(0 ## x)

#define HALT_CODE   0xffffffff

uint32_t reg[32];
uint32_t *mem;
uint32_t mem_size = 0x400000;
uint32_t entry_point = 0x2000;
uint32_t pc;
uint32_t prog_size;
uint32_t mmu_enabled;
int debug_enabled;
long long inst_cnt;

char infile[128];
int show_stat, boot_test;

void print_env(int show_vpc)
{
  fprintf(stderr, "\x1b[1m*** Simulator Status ***\x1b[0m\n");
  if (show_stat) {
    fprintf(stderr, "<register>\n");
    for (int i = 0; i < 16; ++i)
      fprintf(stderr, "  r%-2d: %11d (0x%08x) / r%-2d: %11d (0x%08x)\n",
              i, reg[i], reg[i], i + 16, reg[i + 16], reg[i + 16]);
  }
  if (mmu_enabled) {
    fprintf(stderr, "<Current Virtual PC>: 0x%08x\n", pc);
    if (show_vpc)
      fprintf(stderr, "<Current Physical PC>: 0x%06x\n", pc);
  } else {
    fprintf(stderr, "<Current PC>: 0x%06x\n", pc);
  }
  fprintf(stderr, "<Number of executed instructions>: %lld\n", inst_cnt);
}

void error(char *, ...) __attribute__((noreturn));
void error(char *fmt, ...)
{
  va_list ap;
  va_start(ap, fmt);
  fprintf(stderr, "\x1b[1;31mruntime error: \x1b[39m");
  vfprintf(stderr, fmt, ap);
  fprintf(stderr, "\x1b[0m\n\n");
  print_env(strncmp("to_physical: ", fmt, strlen("to_physical: ")));
  dump_e_i();
  va_end(ap);
  exit(1);
}

enum {
  ALU_IA,
  ALU_C,
};

enum {
  ADD   = B(0000),
  SUB   = B(0001),
  SLL   = B(0010),
  SRL   = B(0011),
  SRA   = B(0100),
  AND   = B(0101),
  OR    = B(0110),
  XOR   = B(0111),
  ADDX4 = B(1000),
  SUBX4 = B(1001),
  MUL   = B(1100),
  MULH  = B(1101),
};

enum {
  EQ  = B(0000),
  NE  = B(0001),
  LT  = B(0010),
  LE  = B(0011),
  ULT = B(0100),
  ULE = B(0101),
  GT  = B(0110),
  UGT = B(0111),
};

uint32_t alu(short type, int func1, int32_t a, int32_t b)
{
  uint32_t ua = a, ub = b;
  uint64_t u64a = a, u64b = b;

  switch (type) {
  case ALU_IA:
    switch (func1) {
    case ADD: return a + b;
    case SUB: return a - b;
    case SLL: return ua << (ub & 31);
    case SRL: return ua >> (ub & 31);
    case SRA: return a >> (ub & 31);
    case AND: return a & b;
    case OR:  return a | b;
    case XOR: return a ^ b;
    case ADDX4: return a + b * 4;
    case SUBX4: return a - b * 4;
    case MUL: return a * b;
    case MULH: return (u64a * u64b) >> 32;
    default: error("unknown integer arithmetic instruction: func1 = %d", func1);
    }
  case ALU_C:
    switch (func1) {
    case EQ: return a == b;
    case NE: return a != b;
    case LT: return a < b;
    case LE: return a <= b;
    case ULT: return ua < ub;
    case ULE: return ua <= ub;
    case GT: return a > b;
    case UGT: return ua >= ub;
    default: error("unknown comparation instruction: func1 = %d", func1);
    }
  default:
    assert(false);
  }
}

void check_addr(uint32_t addr)
{
  if (addr & 3)
    error("load: address must be a multiple of 4: 0x%08x", addr);
  if (addr >= mem_size)
    error("exceeded %dMB limit: 0x%08x", mem_size >> 20, addr);
}

enum {
  IAI = B(000000),
  IAR = B(000001),
  CI  = B(000110),
  CR  = B(000111),
  LI  = B(010010),
  LIH = B(010011),
  LD  = B(011000),
  ST  = B(011001),
  JL  = B(100000),
  JR  = B(100001),
  JEQ = B(101000),
  JNE = B(101001),
  JLT = B(101010),
  JLE = B(101011),
  JGT = B(101100),
  JGE = B(101101),
  SYS = B(110000),
};

/* return 1 when jump instruction is executed */
int exec(uint32_t inst)
{
  int opcode = inst >> 26;
  int func1 = inst & 0xf;
  int32_t imm_n, imm_c, imm_l, imm_s, imm_i;
  int rx = (inst >> 21) & 31, ra = (inst >> 16) & 31, rb = (inst >> 11) & 31;
  int32_t a = reg[ra], b = reg[rb];
  imm_n = (((int32_t)inst) << 11) >> 11;
  imm_c = ((((int32_t)inst) << 6) >> 11) + (inst & 0xffff);
  imm_l = (((int32_t)inst) << 16) >> 16;
  imm_s = ((((int32_t)inst) << 6) >> 16) + (inst & 0x7ff);
  imm_i = (((int32_t)inst) << 16) >> 20;
  switch (opcode) {
  case IAI:
    reg[rx] = alu(ALU_IA, func1, a, imm_i); break;
  case IAR:
    reg[rx] = alu(ALU_IA, func1, a, b); break;
  case CI:
    reg[rx] = alu(ALU_C, func1, a, imm_i); break;
  case CR:
    reg[rx] = alu(ALU_C, func1, a, b); break;
  case LI:
    reg[rx] = imm_n; break;
  case LIH:
    reg[rx] = imm_n << 11; break;
  case LD:
    check_addr(a + imm_l); reg[rx] = mem[(a + imm_l) >> 2]; break;
  case ST:
    check_addr(a + imm_s); mem[(a + imm_l) >> 2] = b; break;
  case JL:
    reg[rx] = pc + 4; pc = pc + 4 + imm_n; return 1;
  case JR:
    reg[rx] = pc + 4; pc = a; return 1;
  case JEQ:
    if (a == 0) pc = pc + 4 + imm_c * 4; return 1;
  case JNE:
    if (a != 0) pc = pc + 4 + imm_c * 4; return 1;
  case JLT:
    if (a < 0) pc = pc + 4 + imm_c * 4; return 1;
  case JLE:
    if (a <= 0) pc = pc + 4 + imm_c * 4; return 1;
  case JGT:
    if (a > 0) pc = pc + 4 + imm_c * 4; return 1;
  case JGE:
    if (a >= 0) pc = pc + 4 + imm_c * 4; return 1;
  case SYS:
    error("SYS opcode unsupported for now");
  default:
    error("unknown opcode = %d", opcode);
  }
  return 0;
}

void init_env()
{
  free(mem);
  mem = malloc(mem_size);
  if (!boot_test)
    reg[30] = reg[31] = mem_size;
  pc = entry_point;
  inst_cnt = 0;
}

void load_file()
{
  FILE *fp = fopen(infile, "r");
  if (fp == NULL)
    error(strerror(errno));

  prog_size = 0;
  for (int i = 0; i < 32; i += 8)
    prog_size += fgetc(fp) << i;

  for (uint32_t i = 0; i < prog_size; ++i) {
    int c = fgetc(fp);
    if (c == EOF)
      error("load_file: reached EOF (actual size is less than header)");
    *((uint8_t*)mem + entry_point + i) = c;
  }

  if (fgetc(fp) != EOF)
    error("load_file: input file remained (actual size is more than header)");
  fclose(fp);
}

void runsim()
{
  init_env();
  load_file();
  while (1) {
    if (debug_enabled)
      debug_hook();
    if (pc >= mem_size)
      error("program counter out of range");
    if (mem[pc >> 2] == HALT_CODE)
      break;
    if (exec(mem[pc >> 2]) == 0)
      pc += 4;
    ++inst_cnt;
  }
}

void print_help(char *prog)
{
  fprintf(stderr, "usage: %s [options] file\n", prog);
  fprintf(stderr, "options:\n");
  fprintf(stderr, "  -boot-test        bootloader test mode\n");
  fprintf(stderr, "  -debug            enable debugging feature\n");
  fprintf(stderr, "  -msize <integer>  change memory size (MB)\n");
  fprintf(stderr, "  -stat             show simulator status\n");
  exit(1);
}

void parse_cmd(int argc, char *argv[])
{
  for (int i = 1; i < argc; ++i) {
    if (strcmp(argv[i], "-boot-test") == 0) {
      entry_point = 0;
      boot_test = 1;
    } else if (strcmp(argv[i], "-debug") == 0) {
      debug_enabled = 1;
    } else if (strcmp(argv[i], "-msize") == 0) {
      if (i == argc - 1) print_help(argv[0]);
      mem_size = atoi(argv[++i]) << 20;
    } else if (strcmp(argv[i], "-stat") == 0) {
      show_stat = 1;
    } else if (infile[0] != '\0') {
      fprintf(stderr, "error: multiple input files are specified\n");
      print_help(argv[0]);
    } else {
      strcpy(infile, argv[i]);
    }
  }
}

int main(int argc, char *argv[])
{
  parse_cmd(argc, argv);
  if (infile[0] == '\0') print_help(argv[0]);
  runsim();
  if (show_stat) {
    print_env(1);
    dump_e_i();
  }
  return 0;
}

