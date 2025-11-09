/*
    Filename: upct.sv
    Author: zlagpacan
    Description: RTL for Upper Program Counter Table
    Spec: LOROF/spec/design/upct.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module upct (

    // seq
    input logic CLK,
    input logic nRST,

    // RESP stage
    input logic                         read_valid_RESP,
    input logic [LOG_UPCT_ENTRIES-1:0]  read_index_RESP,

    output logic [UPCT_ENTRIES-1:0][UPPER_PC_WIDTH-1:0] upct_array,

    // Update 0
    input logic         update0_valid,
    input logic [31:0]  update0_target_full_PC,

    // Update 1
    output logic [LOG_UPCT_ENTRIES-1:0] update1_upct_index
);

    // ----------------------------------------------------------------
    // Signals:

    // FF Array:
    // logic [UPCT_ENTRIES-1:0][UPPER_PC_WIDTH-1:0] upct_array, next_upct_array;
    logic [UPCT_ENTRIES-1:0][UPPER_PC_WIDTH-1:0] next_upct_array;

    // PLRU Arrays:
    logic               plru2, next_plru2;  // index bit 2
    logic [1:0]         plru1, next_plru1;  // index bit 1
    logic [1:0][1:0]    plru0, next_plru0;  // index bit 0

    // Update 0:
    logic [UPPER_PC_WIDTH-1:0]  update0_upper_PC;
    logic [UPCT_ENTRIES-1:0]    update0_matching_upper_PC_by_entry;

    // Update 1:
    logic                           update1_valid;
    logic [UPPER_PC_WIDTH-1:0]      update1_upper_PC;
    logic                           update1_have_match;
    logic [UPCT_ENTRIES-1:0]        update1_matching_upper_PC_by_entry;
    logic [LOG_UPCT_ENTRIES-1:0]    update1_matching_index;

    // ----------------------------------------------------------------
    // Logic: 

    // FF's:
    // always_ff @ (posedge CLK, negedge nRST) begin
    always_ff @ (posedge CLK) begin
        if (~nRST) begin
            upct_array <= '0;

            plru0 <= '0;
            plru1 <= '0;
            plru2 <= '0;

            update1_valid <= 1'b0;
            update1_upper_PC <= '0;
            update1_matching_upper_PC_by_entry <= '1;
        end
        else begin
            upct_array <= next_upct_array;
            
            plru0 <= next_plru0;
            plru1 <= next_plru1;
            plru2 <= next_plru2;

            update1_valid <= update0_valid;
            update1_upper_PC <= update0_upper_PC;
            update1_matching_upper_PC_by_entry <= update0_matching_upper_PC_by_entry;
        end
    end

    // Update 0 Logic:

    assign update0_upper_PC = update0_target_full_PC[31:32-UPPER_PC_WIDTH];

    always_comb begin

        // CAM over entries
        for (int i = 0; i < UPCT_ENTRIES; i++) begin
            update0_matching_upper_PC_by_entry[i] = upct_array[i] == update0_upper_PC;
        end
    end

    // Update 1 and RESP logic:

    // assign observer0_upper_PC_RESP = upct_array[observer0_index_RESP];
    // assign observer1_upper_PC_RESP = upct_array[observer1_index_RESP];

    assign update1_have_match = |update1_matching_upper_PC_by_entry;

    pe_lsb #(
        .WIDTH(8),
        .USE_ONE_HOT(0),
        .USE_INDEX(1)
    ) CAM_PE (
        .req_vec(update1_matching_upper_PC_by_entry),
        .ack_index(update1_matching_index)
    );

    always_comb begin

        // hold array and pointers by default
        next_upct_array = upct_array;
        next_plru2 = plru2;
        next_plru1 = plru1;
        next_plru0 = plru0;

        // advertize PLRU index by default
        update1_upct_index = {plru2, plru1[plru2], plru0[plru2][plru1[plru2]]};

        // check update 1 hit
        if (update1_valid & update1_have_match) begin

            // advertize CAM matching index
            update1_upct_index = update1_matching_index;

            // adjust PLRU following matching index
            next_plru2 = ~update1_matching_index[2];
            next_plru1[update1_matching_index[2]] = ~update1_matching_index[1];
            next_plru0[update1_matching_index[2]][update1_matching_index[1]] = ~update1_matching_index[0];
        end

        // check update 1 miss
        else if (update1_valid & ~update1_have_match) begin

            // advertize PLRU index
            update1_upct_index = {plru2, plru1[plru2], plru0[plru2][plru1[plru2]]};

            // update PLRU array entry
            next_upct_array[update1_upct_index] = update1_upper_PC;

            // adjust PLRU following current PLRU
            next_plru2 = ~plru2;
            next_plru1[plru2] = ~plru1[plru2];
            next_plru0[plru2][plru1[plru2]] = ~plru0[plru2][plru1[plru2]];
        end

        // check RESP access
        else if (read_valid_RESP) begin

            // adjust PLRU following RESP index
            next_plru2 = ~read_index_RESP[2];
            next_plru1[read_index_RESP[2]] = ~read_index_RESP[1];
            next_plru0[read_index_RESP[2]][read_index_RESP[1]] = ~read_index_RESP[0];
        end
    end

endmodule