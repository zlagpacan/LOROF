/*
    Filename: map_table.sv
    Author: zlagpacan
    Description: RTL for Architectural to Physical Register Map Table
    Spec: LOROF/spec/design/map_table.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module map_table #(
    parameter MAP_TABLE_READ_PORT_COUNT = 12,
    parameter MAP_TABLE_WRITE_PORT_COUNT = 4
) (

    // seq
    input logic CLK,
    input logic nRST,

    // read ports
    input logic [MAP_TABLE_READ_PORT_COUNT-1:0][LOG_AR_COUNT-1:0]    read_AR_by_port,
    output logic [MAP_TABLE_READ_PORT_COUNT-1:0][LOG_PR_COUNT-1:0]   read_PR_by_port,

    // write ports
    input logic [MAP_TABLE_WRITE_PORT_COUNT-1:0]                       write_valid_by_port,
    input logic [MAP_TABLE_WRITE_PORT_COUNT-1:0][LOG_AR_COUNT-1:0]     write_AR_by_port,
    input logic [MAP_TABLE_WRITE_PORT_COUNT-1:0][LOG_PR_COUNT-1:0]     write_PR_by_port,

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
        for (int rport = 0; rport < MAP_TABLE_READ_PORT_COUNT; rport++) begin
            read_PR_by_port[rport] = map_table[read_AR_by_port[rport]];
        end
    end

    // map table writes
    always_comb begin
        // low to high port iteration order: higher ports given higher priority
        updated_map_table = map_table;
        for (int wport = 0; wport < MAP_TABLE_WRITE_PORT_COUNT; wport++) begin
            if (write_valid_by_port[wport]) begin
                updated_map_table[write_AR_by_port[wport]] = write_PR_by_port[wport];
            end
        end
    end

    // save map table follows current map table so faster and can perform fine-grain rollback within 4-way as needed
    assign save_map_table = map_table;

    // map table FF logic
    // always_ff @ (posedge CLK, negedge nRST) begin
    always_ff @ (posedge CLK) begin
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