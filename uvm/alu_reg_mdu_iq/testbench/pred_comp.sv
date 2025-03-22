`include "uvm_macros.svh"
import uvm_pkg::*;
`include "sequence_item.sv"


// 38 bit break down
        // 7 bits from ROB INDEX
        // 4 bits for op code
        // 7 bits for register Rd
        // 9 bits for register R1 and its status
        // 9 bits for register R2 and its status
        // 1 bit state of entry
        // 1 bit which pipe it targets
    // 


class node;
    // typedef enum logic [2:0] {
    //     NOTREADY = 3'd0,
    //     READY = 3'd1,
    //     ZERO = 3'd2,
    //     FORWARD = 3'd3
    // } readystate;
    
    // typedef enum logic {
    //     REG = 1'd0,
    //     MDU = 1'd1
    // } state_of_pipe;
    
    localparam NOTREADY = 0;
    localparam READY = 1;
    localparam ZERO = 2;
    localparam FORWARD = 3;
    localparam REG = 0;
    localparam MDU = 1;
    
    typedef struct packed {
        logic [6:0] rob_idx;
        logic [3:0] op_code;
        logic [6:0] rd;
        logic [6:0] r1;
        logic [1:0] r1_state;
        logic [6:0] r2;
        logic [1:0] r2_state;
        logic [6:0] dest;
        logic pipestate;
        // state_of_frame framestate;
    } queue_frame;
    
    queue_frame frame;
    node next;
    function new(alu_reg_mdu_iq_sequence_item t, int way);
        // frame = new; // Allocate memory for the struct
        frame.rob_idx = t.dispatch_ROB_index_by_way[way];
        frame.op_code = t.dispatch_op_by_way[way];
        frame.rd = t.dispatch_dest_PR_by_way[way];
        frame.r1 = t.dispatch_A_PR_by_way[way];
        // A state ...
        frame.r1_state = t.dispatch_A_is_zero_by_way[way] ? ZERO : (t.dispatch_A_ready_by_way[way] ? READY : NOTREADY);
        frame.r2 = t.dispatch_B_PR_by_way[way];
        // B state ...
        frame.r2_state = t.dispatch_B_is_zero_by_way[way] ? ZERO : (t.dispatch_B_ready_by_way[way] ? READY : NOTREADY);
        frame.dest = t.dispatch_dest_PR_by_way[way];
        frame.pipestate = t.dispatch_valid_alu_reg_by_way[way] ? REG : MDU;
        this.next = null;
    endfunction
endclass


class OoO_queue extends uvm_object;
    
`uvm_object_utils(OoO_queue)

    localparam NOTREADY = 0;
    localparam READY = 1;
    localparam ZERO = 2;
    localparam FORWARD = 3;
    localparam REG = 0;
    localparam MDU = 1;
typedef struct packed {
	logic [6:0] rob_idx;
	logic [3:0] op_code;
	logic [6:0] rd;
	logic [6:0] r1;
    logic [1:0] r1_state;
	logic [6:0] r2;
    logic [1:0] r2_state;
	logic [6:0] dest;
    logic pipestate;
    // state_of_frame framestate;
} queue_frame;

    node queue;
    function new(string name = "OoO_queue");
        super.new(name);
    endfunction

    function void print();
        node temp;
        temp = queue;

        while(temp != null) begin
            $display("[temp.frame.r1 = %d]",temp.frame.r1);
            $display("->");
            temp = temp.next;
        end
        $display("null");
    endfunction

    // 1st check what you can dispatch into the queue
    // Check whats forwardable and then check if you can issue 
    // Think about as linked list (pop)
    function void issue(alu_reg_mdu_iq_sequence_item trans);
        bit issued_reg;
        bit issued_mdu;
        node temp = queue;
        if(temp == null) return;

        issued_reg = 1'b0;
        issued_mdu = 1'b0;
        while(temp != null) begin
            if((temp.frame.r1_state == ZERO || temp.frame.r1_state == READY || temp.frame.r1_state == FORWARD)
            && (temp.frame.r2_state == ZERO || temp.frame.r2_state == READY || temp.frame.r2_state == FORWARD)) begin
                // REG OUT
                if(temp.frame.pipestate == REG && trans.alu_reg_pipeline_ready && !issued_reg) begin
                    issued_reg = 1'b1;
                    trans.issue_alu_reg_valid = 1;
                    trans.issue_alu_reg_op = temp.frame.op_code;
                    trans.issue_alu_reg_A_forward = (temp.frame.r1_state == FORWARD);
                    trans.issue_alu_reg_A_is_zero = (temp.frame.r1_state == ZERO);
                    trans.issue_alu_reg_A_bank = (temp.frame.r1[1:0]);
                    trans.issue_alu_reg_B_forward = (temp.frame.r2_state == FORWARD);
                    trans.issue_alu_reg_B_is_zero = (temp.frame.r2_state == ZERO);
                    trans.issue_alu_reg_B_bank = (temp.frame.r2[1:0]);
                    trans.issue_alu_reg_dest_PR = temp.frame.dest;
                    trans.issue_alu_reg_ROB_index = temp.frame.rob_idx;
                    // PRF Outputs
                    trans.PRF_alu_reg_req_A_valid = (temp.frame.r1_state == READY);
                    trans.PRF_alu_reg_req_A_PR = temp.frame.r1;
                    trans.PRF_alu_reg_req_B_valid = (temp.frame.r2_state == READY);
                    trans.PRF_alu_reg_req_B_PR = temp.frame.r2; 
                    delete_queue(temp.frame); // Delete frame
                end

                // MDU OUT
                else if(temp.frame.pipestate == MDU && trans.mdu_pipeline_ready && !issued_mdu) begin
                    issued_mdu = 1'b1;
                    trans.issue_mdu_valid = 1;
                    trans.issue_mdu_op = temp.frame.op_code;
                    trans.issue_mdu_A_forward = (temp.frame.r1_state == FORWARD);
                    trans.issue_mdu_A_is_zero = (temp.frame.r1_state == ZERO);
                    trans.issue_mdu_A_bank = (temp.frame.r1[1:0]);
                    trans.issue_mdu_B_forward = (temp.frame.r2_state == FORWARD);
                    trans.issue_mdu_B_is_zero = (temp.frame.r2_state == ZERO);
                    trans.issue_mdu_B_bank = (temp.frame.r2[1:0]);
                    trans.issue_mdu_dest_PR = temp.frame.dest;
                    trans.issue_mdu_ROB_index = temp.frame.rob_idx;
                    // PRF Outputs
                    trans.PRF_mdu_req_A_valid = (temp.frame.r1_state == READY);
                    trans.PRF_mdu_req_A_PR = temp.frame.r1;
                    trans.PRF_mdu_req_B_valid = (temp.frame.r2_state == READY);
                    trans.PRF_mdu_req_B_PR = temp.frame.r2; 
                    delete_queue(temp.frame); // Delete frame
                end
            end
            temp = temp.next;
        end
    endfunction

    function int dispatch_amount();
        node temp = queue;
        int count = 0;
        if(temp == null) return 8;
        while(temp.next != null) begin
            count += 1;
            temp = temp.next;
        end
        return 8 - count; // how many slots I can dispatch too
    endfunction

    function void insert_queue(alu_reg_mdu_iq_sequence_item trans, int way);
        // Starting from scratch
        if(queue == null) begin
            queue = new(trans,way);
        end
        else begin
            node temp = queue;
            node new_frame = new(trans,way);
            while(temp.next != null) begin
                temp = temp.next;
            end
            temp.next = new_frame;
        end
    endfunction

    function bit frame_comp(queue_frame op1, queue_frame op2);
        return(op1.rob_idx == op2.rob_idx && 
        op1.op_code == op2.op_code && 
        op1.rd == op2.rd &&
        op1.r1 == op2.r1 && 
        op1.r1_state == op2.r1_state && 
        op1.r2 == op2.r2 && 
        op1.r2_state == op2.r2_state && 
        op1.dest == op2.dest && 
        op1.pipestate == op2.pipestate);
    endfunction

    function void delete_queue(queue_frame victim);
        node head;
        node prev;
        bit equal;
        head = queue;
        prev = null;

        if (queue == null) return; // Empty queue case
    
        equal = frame_comp(queue.frame,victim);
        // Case 1: If the head itself holds victim
        if (equal) begin
            queue = queue.next; // Update head to next which should be null
            return;
        end
    
        // Case 2: Searching for the node to delete
        
    
        while (head != null && !equal) begin
            equal = frame_comp(head.frame,victim);
            prev = head;
            head = head.next;
        end
    
        // If found, remove the node
        if (head != null && prev != null) begin
            prev.next = head.next; // Skip the node
        end
    endfunction
    

    function void update_forward(alu_reg_mdu_iq_sequence_item trans);
        logic [3:0] [6:0] wb;
        // intial value
        int k;
        int i;
        int j;
        node temp;
        for(k = 0; k < 4; k++) begin
            wb[k] = 'z;
        end
        
        // Figure out which WB regs 
        for(i = 0; i < 4; i++) begin
            if(trans.WB_bus_valid_by_bank[i]) begin
                wb[i] = {trans.WB_bus_upper_PR_by_bank[i], i[1:0]};
            end
        end

        temp = queue;
        if(temp == null) return;

        for(j = 0; j < 8; j++) begin
            if (temp.frame.r1 === wb[0] || temp.frame.r1 === wb[1] || temp.frame.r1 === wb[2] || temp.frame.r1 === wb[3]) begin
                temp.frame.r1_state = FORWARD;
            end
            if (temp.frame.r2 === wb[0] || temp.frame.r2 === wb[1] || temp.frame.r2 === wb[2] || temp.frame.r2 === wb[3]) begin
                temp.frame.r2_state = FORWARD ;
            end
            if(temp.next != null) temp = temp.next; // move to next frame
        end
    endfunction


    // Actual golden model function
    function void golden(alu_reg_mdu_iq_sequence_item trans);
        // 1st check what you can dispatch into the queue
        // Check whats forwardable and then check if you can issue 
        // Think about as linked list (pop)
        int num_open_frames;
        // INTIAL OUTPUTS
        trans.dispatch_ack_by_way = '0;
        trans.issue_alu_reg_valid = '0;
        trans.issue_alu_reg_op = '0;
        trans.issue_alu_reg_A_forward = '0;
        trans.issue_alu_reg_A_is_zero = '0;
        trans.issue_alu_reg_A_bank = '0;
        trans.issue_alu_reg_B_forward = '0;
        trans.issue_alu_reg_B_is_zero = '0;
        trans.issue_alu_reg_B_bank = '0;
        trans.issue_alu_reg_dest_PR = '0;
        trans.issue_alu_reg_ROB_index = '0;
        trans.PRF_alu_reg_req_A_valid = '0;
        trans.PRF_alu_reg_req_A_PR = '0;
        trans.PRF_alu_reg_req_B_valid = '0;
        trans.PRF_alu_reg_req_B_PR = '0;
        trans.issue_mdu_valid = '0;
        trans.issue_mdu_op = '0;
        trans.issue_mdu_A_forward = '0;
        trans.issue_mdu_A_is_zero = '0;
        trans.issue_mdu_A_bank = '0;
        trans.issue_mdu_B_forward = '0;
        trans.issue_mdu_B_is_zero = '0;
        trans.issue_alu_reg_B_is_zero = '0;
        trans.issue_mdu_B_bank = '0;
        trans.issue_mdu_dest_PR = '0;
        trans.issue_mdu_ROB_index = '0;
        trans.PRF_mdu_req_A_valid = '0;
        trans.PRF_mdu_req_A_PR = '0;
        trans.PRF_mdu_req_B_valid = '0;
        trans.PRF_mdu_req_B_PR = '0;
      
    
        // # of frames that are open
        num_open_frames = dispatch_amount();

        // update status of queue
        update_forward(trans);

        print();

        // issuing 
        issue(trans); 

        // Dispatching into queue
        for(int i = 0; i < 4; i++) begin
            if(num_open_frames > 0 && num_open_frames <= 8) begin // Needs to be less than 8 frames
                if(trans.dispatch_attempt_by_way[i]) begin
                    trans.dispatch_ack_by_way[i] = 1;
                    num_open_frames --;
                    if(trans.dispatch_valid_alu_reg_by_way[i]) begin
                        insert_queue(trans,i); 
                    end
                    else if(trans.dispatch_valid_mdu_by_way[i]) begin
                        insert_queue(trans,i);
                    end
                end
            end
        end
    endfunction

endclass: OoO_queue