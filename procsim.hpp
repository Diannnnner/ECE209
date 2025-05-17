#ifndef PROCSIM_HPP
#define PROCSIM_HPP

#include <cstdint>
#include <cstdio>

#define DEFAULT_K0 1
#define DEFAULT_K1 2
#define DEFAULT_K2 3
#define DEFAULT_R 8
#define DEFAULT_F 4

typedef struct _proc_inst_t
{
    uint32_t instruction_address;
    int32_t op_code;
    int32_t src_reg[2];
    int32_t dest_reg;
    
    // You may introduce other fields as needed
    uint64_t tag;
} proc_inst_t;

typedef struct _proc_stats_t
{
    float avg_inst_retired;
    float avg_inst_fired;
    float avg_disp_size;
    unsigned long max_disp_size;
    unsigned long retired_instruction;
    unsigned long cycle_count;
} proc_stats_t;

typedef struct _proc_t
{
    uint64_t cdb_size;
    uint64_t k0_size;
    uint64_t k1_size;
    uint64_t k2_size;
    uint64_t fetch_width;
} proc_t;

typedef struct _proc_rs_entry_t
{
    bool valid;
    bool next_valid;
    bool busy[2];
    bool next_busy[2];
    proc_inst_t inst;
    uint64_t blocking_inst[2];
    bool executed;
} proc_rs_entry_t;

typedef struct _proc_exec_entry_t
{
    uint64_t tag;
    uint64_t index;
} proc_exec_entry_t;

typedef struct _proc_rob_entry_t
{
    proc_inst_t inst;
    bool finish;
} proc_rob_entry_t;

typedef struct _proc_reg_table_entry_t
{
    bool free;
    uint64_t tag;
} proc_reg_table_entry_t;

bool read_instruction(proc_inst_t* p_inst);

void setup_proc(uint64_t r, uint64_t k0, uint64_t k1, uint64_t k2, uint64_t f);
void run_proc(proc_stats_t* p_stats);
void complete_proc(proc_stats_t* p_stats);

#endif /* PROCSIM_HPP */