/*
    Filename: ready_table.sv
    Author: zlagpacan
    Description: RTL for Physical Register Ready Table
    Spec: LOROF/spec/design/ready_table.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module ready_table (

    // seq
    input logic CLK,
    input logic nRST,

    // 8x read ports
    input logic [7:0][LOG_PR_COUNT-1:0]     read_PR_by_port,
    output logic [7:0]                      read_ready_by_port,

    // 4x set ports
    input logic [3:0]                       set_valid_by_port,
    input logic [3:0][LOG_PR_COUNT-1:0]     set_PR_by_port,

    // 4x clear ports
    input logic [3:0]                       clear_valid_by_port,
    input logic [3:0][LOG_PR_COUNT-1:0]     clear_PR_by_port
);

    // ----------------------------------------------------------------
    // Signals:

    // ready table FF array
    logic [PR_COUNT-1:0] ready_table, next_ready_table;

    // ----------------------------------------------------------------
    // Logic:

    // reads
    always_comb begin
        for (int rport = 0; rport < 8; rport++) begin
            read_ready_by_port[rport] = next_ready_table[read_PR_by_port[rport]];
        end
    end

    // writes
    always_comb begin

        // start with prev state
        next_ready_table = ready_table;

        // go through set's
        for (int sport = 0; sport < 4; sport++) begin
            if (set_valid_by_port[sport]) begin
                next_ready_table[set_PR_by_port[sport]] = 1'b1;
            end
        end

        // go through clear's
        for (int cport = 0; cport < 4; cport++) begin
            if (clear_valid_by_port[cport]) begin
                next_ready_table[clear_PR_by_port[cport]] = 1'b0; 
            end
        end
    end

    // FF Logic
    always_ff @ (posedge CLK, negedge nRST) begin
    // always_ff @ (posedge CLK) begin
        if (~nRST) begin
            // first PR's corresonding to AR's start ready
            for (int pr = 0; pr < AR_COUNT; pr++) begin
                ready_table[pr] <= 1'b1;
            end
            // remaining PR's start not ready
            for (int pr = AR_COUNT; pr < PR_COUNT; pr++) begin
                ready_table[pr] <= 1'b0;
            end
        end
        else begin
            ready_table <= next_ready_table;
        end
    end

endmodule