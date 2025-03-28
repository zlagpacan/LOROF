/*
    Filename: map_table.sv
    Author: zlagpacan
    Description: RTL for Architectural to Physical Register Map Table
    Spec: LOROF/spec/design/map_table.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module map_table (

    // seq
    input logic CLK,
    input logic nRST,

    // 12x read ports
    input logic [11:0][LOG_AR_COUNT-1:0]    read_AR_by_port,
    output logic [11:0][LOG_PR_COUNT-1:0]   read_PR_by_port,

    // 4x write ports
    input logic [3:0]                       write_valid_by_port,
    input logic [3:0][LOG_AR_COUNT-1:0]     write_AR_by_port,
    input logic [3:0][LOG_PR_COUNT-1:0]     write_PR_by_port,

    // checkpoint save
    output logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0]   save_map_table,

    // checkpoint restore
    input logic                                     restore_valid,
    input logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0]    restore_map_table
);

    // ----------------------------------------------------------------
    // Signals:

    // map table FF array
    logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0]  map_table;

    // map table with write updates
    logic [AR_COUNT-1:0][LOG_PR_COUNT-1:0]  updated_map_table;

    // ----------------------------------------------------------------
    // Logic: 

    // map table reads
    always_comb begin
        for (int rport = 0; rport < 12; rport++) begin
            read_PR_by_port[rport] = map_table[read_AR_by_port[rport]];
        end
    end

    // map table writes
    always_comb begin
        // low to high port iteration order: higher ports given higher priority
        updated_map_table = map_table;
        for (int wport = 0; wport < 4; wport++) begin
            if (write_valid_by_port[wport]) begin
                updated_map_table[write_AR_by_port[wport]] = write_PR_by_port[wport];
            end
        end
    end

    // save map table follows updated map table with writes
    assign save_map_table = updated_map_table;

    // map table FF logic
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            // init: map AR to equivalent value PR
            for (int ar = 0; ar < AR_COUNT; ar++) begin
                map_table[ar] <= ar;
            end
        end
        else begin
            if (restore_valid) begin
                map_table <= restore_map_table;
            end
            else begin
                map_table <= updated_map_table;
            end
        end
    end

endmodule