/*
    Filename: ar_dep_check.sv
    Author: zlagpacan
    Description: RTL for Architectural Register Dependence Checker
    Spec: LOROF/spec/design/ar_dep_check.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module ar_dep_check (

    // inputs by way
    input logic [3:0][4:0]  A_AR_by_way,
    input logic [3:0][4:0]  B_AR_by_way,
    input logic [3:0]       regwrite_by_way,
    input logic [3:0][4:0]  dest_AR_by_way,

    // outputs by way
    output logic [3:0]          A_PR_dep_by_way,
    output logic [3:0][1:0]     A_PR_sel_by_way,
    output logic [3:0]          B_PR_dep_by_way,
    output logic [3:0][1:0]     B_PR_sel_by_way,
    output logic [3:0]          dest_PR_dep_by_way,
    output logic [3:0][1:0]     dest_PR_sel_by_way
);

    // interested in RAW and WAW hazards

    // ----------------------------------------------------------------
    // Logic:
        
    // no deps for way 0
    assign A_PR_dep_by_way[0] = 1'b0;
    assign A_PR_sel_by_way[0] = 2'h0;
    assign B_PR_dep_by_way[0] = 1'b0;
    assign B_PR_sel_by_way[0] = 2'h0;
    assign dest_PR_dep_by_way[0] = 1'b0;
    assign dest_PR_sel_by_way[0] = 2'h0;

    // way 1 can dep on way 0:
    always_comb begin

        // A RAW
        if (regwrite_by_way[0] & (dest_AR_by_way[0] == A_AR_by_way[1])) begin
            A_PR_dep_by_way[1] = 1'b1;
            A_PR_sel_by_way[1] = 2'h0;
        end
        else begin
            A_PR_dep_by_way[1] = 1'b0;
            A_PR_sel_by_way[1] = 2'h0;
        end
        
        // B RAW
        if (regwrite_by_way[0] & (dest_AR_by_way[0] == B_AR_by_way[1])) begin
            B_PR_dep_by_way[1] = 1'b1;
            B_PR_sel_by_way[1] = 2'h0;
        end
        else begin
            B_PR_dep_by_way[1] = 1'b0;
            B_PR_sel_by_way[1] = 2'h0;
        end

        // dest WAW
        if (regwrite_by_way[0] & (dest_AR_by_way[0] == dest_AR_by_way[1])) begin
            dest_PR_dep_by_way[1] = 1'b1;
            dest_PR_sel_by_way[1] = 2'h0;
        end
        else begin
            dest_PR_dep_by_way[1] = 1'b0;
            dest_PR_sel_by_way[1] = 2'h0;
        end
    end

    // way 2 can dep on ways 1, 0:
    always_comb begin

        // A RAW
        if (regwrite_by_way[1] & (dest_AR_by_way[1] == A_AR_by_way[2])) begin
            A_PR_dep_by_way[2] = 1'b1;
            A_PR_sel_by_way[2] = 2'h1;
        end
        else if (regwrite_by_way[0] & (dest_AR_by_way[0] == A_AR_by_way[2])) begin
            A_PR_dep_by_way[2] = 1'b1;
            A_PR_sel_by_way[2] = 2'h0;
        end
        else begin
            A_PR_dep_by_way[2] = 1'b0;
            A_PR_sel_by_way[2] = 2'h0;
        end

        // B RAW
        if (regwrite_by_way[1] & (dest_AR_by_way[1] == B_AR_by_way[2])) begin
            B_PR_dep_by_way[2] = 1'b1;
            B_PR_sel_by_way[2] = 2'h1;
        end
        else if (regwrite_by_way[0] & (dest_AR_by_way[0] == B_AR_by_way[2])) begin
            B_PR_dep_by_way[2] = 1'b1;
            B_PR_sel_by_way[2] = 2'h0;
        end
        else begin
            B_PR_dep_by_way[2] = 1'b0;
            B_PR_sel_by_way[2] = 2'h0;
        end

        // dest WAW
        if (regwrite_by_way[1] & (dest_AR_by_way[1] == dest_AR_by_way[2])) begin
            dest_PR_dep_by_way[2] = 1'b1;
            dest_PR_sel_by_way[2] = 2'h1;
        end
        else if (regwrite_by_way[0] & (dest_AR_by_way[0] == dest_AR_by_way[2])) begin
            dest_PR_dep_by_way[2] = 1'b1;
            dest_PR_sel_by_way[2] = 2'h0;
        end
        else begin
            dest_PR_dep_by_way[2] = 1'b0;
            dest_PR_sel_by_way[2] = 2'h0;
        end
    end

    // way 3 can dep on ways 2, 1, 0:
    always_comb begin

        // A RAW
        if (regwrite_by_way[2] & (dest_AR_by_way[2] == A_AR_by_way[3])) begin
            A_PR_dep_by_way[3] = 1'b1;
            A_PR_sel_by_way[3] = 2'h2;
        end
        else if (regwrite_by_way[1] & (dest_AR_by_way[1] == A_AR_by_way[3])) begin
            A_PR_dep_by_way[3] = 1'b1;
            A_PR_sel_by_way[3] = 2'h1;
        end
        else if (regwrite_by_way[0] & (dest_AR_by_way[0] == A_AR_by_way[3])) begin
            A_PR_dep_by_way[3] = 1'b1;
            A_PR_sel_by_way[3] = 2'h0;
        end
        else begin
            A_PR_dep_by_way[3] = 1'b0;
            A_PR_sel_by_way[3] = 2'h0;
        end

        // B RAW
        if (regwrite_by_way[2] & (dest_AR_by_way[2] == B_AR_by_way[3])) begin
            B_PR_dep_by_way[3] = 1'b1;
            B_PR_sel_by_way[3] = 2'h2;
        end
        else if (regwrite_by_way[1] & (dest_AR_by_way[1] == B_AR_by_way[3])) begin
            B_PR_dep_by_way[3] = 1'b1;
            B_PR_sel_by_way[3] = 2'h1;
        end
        else if (regwrite_by_way[0] & (dest_AR_by_way[0] == B_AR_by_way[3])) begin
            B_PR_dep_by_way[3] = 1'b1;
            B_PR_sel_by_way[3] = 2'h0;
        end
        else begin
            B_PR_dep_by_way[3] = 1'b0;
            B_PR_sel_by_way[3] = 2'h0;
        end

        // dest WAW
        if (regwrite_by_way[2] & (dest_AR_by_way[2] == dest_AR_by_way[3])) begin
            dest_PR_dep_by_way[3] = 1'b1;
            dest_PR_sel_by_way[3] = 2'h2;
        end
        else if (regwrite_by_way[1] & (dest_AR_by_way[1] == dest_AR_by_way[3])) begin
            dest_PR_dep_by_way[3] = 1'b1;
            dest_PR_sel_by_way[3] = 2'h1;
        end
        else if (regwrite_by_way[0] & (dest_AR_by_way[0] == dest_AR_by_way[3])) begin
            dest_PR_dep_by_way[3] = 1'b1;
            dest_PR_sel_by_way[3] = 2'h0;
        end
        else begin
            dest_PR_dep_by_way[3] = 1'b0;
            dest_PR_sel_by_way[3] = 2'h0;
        end
    end

endmodule