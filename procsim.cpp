#include "procsim.hpp"
#include <cstdio>
#include <cinttypes>
#include <cstdlib>
#include <cstring>
#include <unistd.h>
#include <queue>
#include <iostream>
#include <iomanip>
#include <fstream>
#include <vector>
#include <queue>
#include <stack>
#include <string>
#include <cstring>
#include <cstdlib>
#include <algorithm>
#include <map>
#include <unordered_map>
#include <set>

using namespace std;
proc_t processor;
std::vector<proc_inst_t> dispatch_queue;
std::vector<proc_rs_entry_t> scheduling_queue;
std::vector<bool> valid_register;
vector<proc_rob_entry_t> ROB;
uint64_t gen_tag;
int execute_count[3];
std::queue<proc_rs_entry_t> result_bus_shifter;

std::vector<vector<int>> debug_table(6, vector<int>(100000));
std::vector<int> instruction_counter(5, 1);
int cycles_counter;
uint64_t max_dispatch_queue_size = 0;
uint64_t num_dispatch_queue = 0;
uint64_t average_dispatch_queue_size = 0;
uint64_t num_fired_instructions;
int debug_cycle = 155;

/**
 * Subroutine for initializing the processor. You many add and initialize any global or heap
 * variables as needed.
 * XXX: You're responsible for completing this routine
 *
 * @r ROB size
 * @k0 Number of k0 FUs
 * @k1 Number of k1 FUs
 * @k2 Number of k2 FUs
 * @f Number of instructions to fetch
 */
void setup_proc(uint64_t r, uint64_t k0, uint64_t k1, uint64_t k2, uint64_t f) 
{
    memset(&processor, 0, sizeof(proc_t));
    processor.cdb_size = r;
    processor.k0_size = k0;
    processor.k1_size = k1;
    processor.k2_size = k2;
    processor.fetch_width = f;

    for (uint64_t i = 0; i < 2 * (processor.k0_size + processor.k1_size + processor.k2_size); i++)
    {
        proc_rs_entry_t scheduling_queue_entry;
        scheduling_queue_entry.valid = false;
        scheduling_queue_entry.next_valid = false;
        scheduling_queue_entry.busy[0] = false;
        scheduling_queue_entry.busy[1] = false;
        scheduling_queue_entry.next_busy[0] = false;
        scheduling_queue_entry.next_busy[1] = false;
        scheduling_queue.push_back(scheduling_queue_entry);
        valid_register.push_back(false);
    }

    execute_count[0] = processor.k0_size;
    execute_count[1] = processor.k1_size;
    execute_count[2] = processor.k2_size;

    gen_tag = 1;
    num_fired_instructions = 0;
    cycles_counter = 1;
}

// helper to process one fetched instruction
bool fetch_and_record(proc_inst_t& inst)
{
    if (!read_instruction(&inst)) return false;

    int index = instruction_counter[0];
    debug_table[0][index] = index;
    debug_table[1][index] = cycles_counter;
    instruction_counter[0]++;
    return true;
}

// fetch multiple instructions into buffer
bool fetch_inst(proc_inst_t* insts)
{
    int fetched = 0;

    for (uint64_t i = 0; i < processor.fetch_width; ++i)
    {
        bool success = fetch_and_record(insts[i]);
        if (!success) break;
        ++fetched;
    }

    return (fetched > 0);
}


// add instructions to dispatch queue and ROB
/*Dispatch*/
void dispatch_queue_push(proc_inst_t* p_inst, bool start_dispatch)
{
    if (!start_dispatch) return;

    for (uint64_t i = 0; i < processor.fetch_width; i++)
    {
        uint64_t current_tag = gen_tag;

        p_inst[i].tag = current_tag;
        dispatch_queue.push_back(p_inst[i]);

        proc_rob_entry_t new_entry;
        new_entry.inst = p_inst[i];
        new_entry.inst.tag = current_tag;
        new_entry.finish = false;
        ROB.push_back(new_entry);

        debug_table[2][current_tag] = cycles_counter;

        std::cerr << "[debug] in dispatch_queue_push: dispatch_queue.push_back triggered on cycle " << cycles_counter << endl;
        gen_tag++;
    }

    size_t current_size = dispatch_queue.size();
    if (current_size > max_dispatch_queue_size)
    {
        max_dispatch_queue_size = current_size;
    }
}


int32_t rs_available()
{
    for (uint64_t i = 0; i < scheduling_queue.size(); i++)
    {
        if (!scheduling_queue[i].valid)
        {
            return (int32_t)i;
        }
    }
    return -1;
}

// find rob entry by tag
int ROB_lookup(uint64_t tag)
{
    int idx = 0;
    for (const auto& entry : ROB)
    {
        if (entry.inst.tag == tag) return idx;
        ++idx;
    }
    return -1;
}



// check RAW hazard for src0
int check_data_dependency_0(proc_inst_t* inst)
{
    int rob_idx = ROB_lookup(inst->tag);
    if (rob_idx <= 0) return -1;

    int target = inst->src_reg[0];

    for (int i = rob_idx - 1; i >= 0; --i)
    {
        const auto& entry = ROB[i].inst;
        if (entry.dest_reg == -1) continue;
        if (entry.dest_reg != target) continue;

        if (ROB[i].finish) return -1;
        return i;
    }
    return -1;
}


// check RAW hazard for src1
int check_data_dependency_1(proc_inst_t* inst)
{
    int ROB_index = ROB_lookup(inst->tag);
    if (ROB_index < 1)
    {
        return -1;
    }
    for (int i = ROB_index - 1; i >= 0; i--)
    {
        if ((ROB[i].inst.dest_reg != -1)){
            if ((ROB[i].inst.dest_reg == inst->src_reg[1]))
            {
                if (ROB[i].finish)
                {
                    return -1;
                }
                else {
                    return (int) i;
                }
            }
        }
        
    }
    return -1;
}

// check dependency and move to rs
/*Schedule*/

void schedule_inst()
{
    if (dispatch_queue.empty()) return;

    int32_t index = rs_available();
    
    while (index >= 0 && !dispatch_queue.empty()) {
        proc_inst_t inst = dispatch_queue.front();  // 
        dispatch_queue.erase(dispatch_queue.begin());

        int dep0 = check_data_dependency_0(&inst);
        int dep1 = check_data_dependency_1(&inst);

        proc_rs_entry_t entry;
        entry.inst = inst;
        entry.valid = true;
        entry.next_valid = true;
        entry.executed = false;

        // src0 hazard check
        if (dep0 != -1) {
            entry.busy[0] = true;
            entry.next_busy[0] = true;
            entry.blocking_inst[0] = ROB[dep0].inst.tag;
        } else {
            entry.busy[0] = false;
        }

        // src1 hazard check
        if (dep1 != -1) {
            entry.busy[1] = true;
            entry.next_busy[1] = true;
            entry.blocking_inst[1] = ROB[dep1].inst.tag;
        } else {
            entry.busy[1] = false;
        }

        scheduling_queue[index] = entry;
        valid_register[index] = true;

        debug_table[3][inst.tag] = cycles_counter;

        index = rs_available();  // 
    }
}


// clear busy bits when dependency done
void wakeup_scheduling_queue(proc_rob_entry_t* rob_entry)
{
    uint64_t tag = rob_entry->inst.tag;

    for (auto& entry : scheduling_queue)
    {
        if (!entry.valid) continue;

        bool match0 = (entry.busy[0] && entry.blocking_inst[0] == tag);
        bool match1 = (entry.busy[1] && entry.blocking_inst[1] == tag);

        if (match0 || match1)
        {
            if (match0) entry.next_busy[0] = false;
            if (match1) entry.next_busy[1] = false;
        }
    }
}


bool comp(proc_exec_entry_t a, proc_exec_entry_t b) {
    return a.tag < b.tag;
}

// issue ready instructions to functional units
/*Execute*/
void execute()
{
    bool has_valid = any_of(scheduling_queue.begin(), scheduling_queue.end(),
                            [](const proc_rs_entry_t& e) { return e.valid; });
    if (!has_valid) return;

    std::vector<proc_exec_entry_t> exec_ready;
    for (size_t idx = 0; idx < scheduling_queue.size(); ++idx) {
        auto& entry = scheduling_queue[idx];
        if (entry.valid && !entry.busy[0] && !entry.busy[1] && !entry.executed) {
            proc_exec_entry_t e;
            e.index = idx;
            e.tag = entry.inst.tag;
            exec_ready.push_back(e);
        }
    }
    

    std::sort(exec_ready.begin(), exec_ready.end(), comp);

    for (const auto& task : exec_ready) {
        int fu_type = (scheduling_queue[task.index].inst.op_code == -1) ? 1 : scheduling_queue[task.index].inst.op_code;
        if (execute_count[fu_type] <= 0) continue;

        scheduling_queue[task.index].executed = true;
        num_fired_instructions++;
        debug_table[4][scheduling_queue[task.index].inst.tag] = cycles_counter;
        execute_count[fu_type]--;
        result_bus_shifter.push(scheduling_queue[task.index]);
    }
}



// retire head of rob
void ROB_commit(proc_stats_t* p_stats)
{
    ROB.erase(ROB.begin());
    p_stats->retired_instruction++;
}

// update rob and wakeup logic
/*State Update*/

void state_update(proc_stats_t* p_stats)
{
    // phase 1: update RS busy/valid bits
    for (size_t i = 0; i < scheduling_queue.size(); ++i)
    {
        auto& entry = scheduling_queue[i];

        bool valid = entry.valid;
        if (valid && entry.busy[0] && !entry.next_busy[0]) {
            entry.busy[0] = false;
        }
        if (valid && entry.busy[1] && !entry.next_busy[1]) {
            entry.busy[1] = false;
        }

        if (!valid_register[i]) {
            entry.valid = false;
        }
        if (!entry.next_valid) {
            valid_register[i] = false;
        }
    }

    if (result_bus_shifter.empty()) return;

    // phase 2: broadcast results via result bus
    int cdb_slots = processor.cdb_size;
    while (cdb_slots-- > 0 && !result_bus_shifter.empty())
    {
        auto entry = result_bus_shifter.front();
        result_bus_shifter.pop();

        for (size_t i = 0; i < scheduling_queue.size(); ++i)
        {
            auto& target = scheduling_queue[i];
            if (entry.inst.tag != target.inst.tag) continue;

            target.next_valid = false;

            int rob_idx = ROB_lookup(target.inst.tag);
            auto& rob_entry = ROB[rob_idx];
            rob_entry.finish = true;

            int fu = rob_entry.inst.op_code;
            if (fu == -1) fu = 1;
            execute_count[fu]++;

            wakeup_scheduling_queue(&rob_entry);
            debug_table[5][rob_entry.inst.tag] = cycles_counter;
            break;
        }
    }

    // phase 3: commit from ROB
    while (!ROB.empty() && ROB.front().finish)
    {
        ROB_commit(p_stats);
    }
}

/**
 * Subroutine that simulates the processor.
 *   The processor should fetch instructions as appropriate, until all instructions have executed
 * XXX: You're responsible for completing this routine
 *
 * @p_stats Pointer to the statistics structure
 */
void run_proc(proc_stats_t* p_stats)
{
    proc_inst_t fetch_buffer[processor.fetch_width];
    proc_inst_t dispatch_buffer[processor.fetch_width];

    bool fetching = true;
    bool dispatching = false;

    while (true)
    {
        // pipeline stages
        state_update(p_stats);
        execute();
        schedule_inst();

        // dispatch
        dispatch_queue_push(dispatch_buffer, dispatching);
        average_dispatch_queue_size += dispatch_queue.size();

        // fetch
        if (fetching)
        {
            fetching = fetch_inst(fetch_buffer);

            if (fetching)
            {
                std::memcpy(dispatch_buffer, fetch_buffer, sizeof(fetch_buffer));
                dispatching = true;
            }
            else
            {
                dispatching = false;
            }
        }
        else
        {
            dispatching = false;
        }

        // bookkeeping
        ++p_stats->cycle_count;
        ++cycles_counter;

        // termination
        if (p_stats->retired_instruction >= 100000)
            break;
    }
}


/**
 * Subroutine for cleaning up any outstanding instructions and calculating overall statistics
 * such as average IPC, average fire rate etc.
 * XXX: You're responsible for completing this routine
 *
 * @p_stats Pointer to the statistics structure
 */
void complete_proc(proc_stats_t *p_stats) 
{
    p_stats->max_disp_size = max_dispatch_queue_size;
    p_stats->avg_disp_size = (float) average_dispatch_queue_size / (float) p_stats->cycle_count;
    p_stats->avg_inst_fired = (float) num_fired_instructions / (float) p_stats->cycle_count;
    p_stats->avg_inst_retired = (float) p_stats->retired_instruction / (float) p_stats->cycle_count;
    ofstream file("mcf.output");
    file << "Processor Settings\n";
    file << "R: " << processor.cdb_size << "\n";
    file << "k0: " << processor.k0_size << "\n";
    file << "k1: " << processor.k1_size << "\n";
    file << "k2: " << processor.k2_size << "\n";
    file << "F: "  << processor.fetch_width << "\n";
    file << "\n";
    file << "INST	FETCH	DISP	SCHED	EXEC	STATE\n";
    for (int i = 1; i < 100001; i++)
    {
        for (int j = 0; j < 5; j++)
        {
            file << debug_table[j][i] << "	";
        }
        file << debug_table[5][i];
        file <<"\n";
    }
    file << "\n";
    file << "Processor stats:\n";
	file << "Total instructions: " << p_stats->retired_instruction << "\n";
    file << "Avg Dispatch queue size: " << fixed << setprecision(6) << p_stats->avg_disp_size << "\n";
    file << "Maximum Dispatch queue size: " << p_stats->max_disp_size << "\n";
    file << "Avg inst fired per cycle: " << p_stats->avg_inst_fired << "\n";
	file << "Avg inst retired per cycle: " << p_stats->avg_inst_retired << "\n";
	file << "Total run time (cycles): " << p_stats->cycle_count << "\n";
    file.close();
}