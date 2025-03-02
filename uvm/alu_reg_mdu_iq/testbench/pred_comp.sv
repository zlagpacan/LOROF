`include "uvm_macros.svh"
import uvm_pkg::*;

typedef enum logic [1:0] {
    NOTREADY = 2'd0;
    READY = 2'd1;
    FORWARD = 2'd2
} readystate_t;

typedef enum logic [1:0] {
    INVALID = 2'd0;
    VALID = 2'd1;
    ISSUED = 2'd2;
} state_of_frame;

typedef enum logic {
    REG = 1'd0;
    MUL_DIV = 1'd1;
} state_of_pipe;


typedef struct packed {
	logic [6:0] rob_idx;
	logic [3:0] op_code;
	logic [6:0] rd;
	logic [6:0] r1;
    readystate_t r1_state;
	logic [6:0] r2;
    readystate_t r2_state;
    state_of_pipe pipestate;
    state_of_frame framestate;
} queue_frame;

class OoO_queue extends uvm_object;
    `uvm_object_utils(OoO_queue);
    // 38 bit break down
        // 7 bits from ROB INDEX
        // 4 bits for op code
        // 7 bits for register Rd
        // 9 bits for register R1 and its status
        // 9 bits for register R2 and its status
        // 1 bit state of entry
        // 1 bit which pipe it targets
    // 
    queue_frame [7:0] queue;

    function new(string name = "OoO_queue", uvm_component parent);
        super.new(name, parent);
    endfunction: new

    function logic [3:0] count_invalid();
        logic [3:0] count;
        for(int i = 0; i < 8; i++) begin
            if(queue.framestate == INVALID) begin
                count++;
            end
        end
        return count;
    endfunction

    function void populate_queue(logic [3:0] attempt_by_way, // PICK UP HERE
    logic [3:0] op_by_way, );

    endfunction

    
endclass: OoO_queue
