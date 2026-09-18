/*
    Filename: rat.sv
    Author: zlagpacan
    Description: RTL for Register Alias Table (ar to pr)
    Spec: LOROF/spec/design/rat.md
*/

`include "corep.vh"

module rat #(
    // hardcode 4-way irat, 1-way frat
) (
    // seq
    input logic CLK,
    input logic nRST,

    // irat reads
    input corep::ar5_t [3:0]    irat_A_ar5_by_way,
    output corep::pr_t [3:0]    irat_A_pr_by_way,

    input corep::ar5_t [3:0]    irat_B_ar5_by_way,
    output corep::pr_t [3:0]    irat_B_pr_by_way,

    // irat writes
    input logic [3:0]           irat_dest_write_valid_by_way,
    input corep::ar5_t [3:0]    irat_dest_ar5_by_way,
    output corep::pr_t [3:0]    irat_dest_old_pr_by_way,
    input corep::pr_t [3:0]     irat_dest_new_pr_by_way,

    // frat reads
    input corep::ar5_t [3:0]    frat_A_ar5_by_way,
    output corep::pr_t [3:0]    frat_A_pr_by_way,

    input corep::ar5_t [3:0]    frat_B_ar5_by_way,
    output corep::pr_t [3:0]    frat_B_pr_by_way,

    input corep::ar5_t [3:0]    frat_C_ar5_by_way,
    output corep::pr_t [3:0]    frat_C_pr_by_way,

    // frat writes
    input logic [3:0]           frat_dest_write_valid_by_way,
    input corep::ar5_t [3:0]    frat_dest_ar5_by_way,
    output corep::pr_t [3:0]    frat_dest_old_pr_by_way,
    input corep::pr_t [3:0]     frat_dest_new_pr_by_way,

    // instr yields
    input logic [3:0]   instr_is_fp_by_way,
    output logic [3:0]  instr_yield_by_way,

    // checkpoint save
    output corep::irat_t    save_irat,
    output corep::frat_t    save_frat,

    // checkpoint restore
    input logic             restore_valid,
    input corep::irat_t     restore_irat,
    input corep::frat_t     restore_frat
);

    // ----------------------------------------------------------------
    // Signals:

    // rat arrays
    corep::irat_t irat;

    corep::frat_t frat;

    // rat reads
    corep::pr_t [3:0] read_irat_A_pr_by_way;
    corep::pr_t [3:0] read_irat_B_pr_by_way;
    corep::pr_t [3:0] read_irat_dest_old_pr_by_way;
    
    corep::pr_t [3:0] read_frat_A_pr_by_way;
    corep::pr_t [3:0] read_frat_B_pr_by_way;
    corep::pr_t [3:0] read_frat_C_pr_by_way;
    corep::pr_t [3:0] read_frat_dest_old_pr_by_way;

    // ----------------------------------------------------------------
    // Logic: 

    // rat reads
    always_comb begin
        for (int way = 0; way < 4; way++) begin
            read_irat_A_pr_by_way[way] = irat[irat_A_ar5_by_way[way]];
            read_irat_B_pr_by_way[way] = irat[irat_B_ar5_by_way[way]];
            read_irat_dest_old_pr_by_way[way] = irat[irat_dest_ar5_by_way[way]];
            
            read_frat_A_pr_by_way[way] = frat[frat_A_ar5_by_way[way]];
            read_frat_B_pr_by_way[way] = frat[frat_B_ar5_by_way[way]];
            read_frat_C_pr_by_way[way] = frat[frat_C_ar5_by_way[way]];
            read_frat_dest_old_pr_by_way[way] = frat[frat_dest_ar5_by_way[way]];
        end
    end

    // rat bypassing
    always_comb begin
        
        // no deps for way 0:
        irat_A_pr_by_way[0] = read_irat_A_pr_by_way[0];
        irat_B_pr_by_way[0] = read_irat_B_pr_by_way[0];
        irat_dest_old_pr_by_way[0] = read_irat_dest_old_pr_by_way[0];

        A_pr_by_way[0] = read_A_pr_by_way[0];
        B_pr_by_way[0] = read_B_pr_by_way[0];
        C_pr_by_way[0] = read_C_pr_by_way[0];
        dest_old_pr_by_way[0] = read_dest_old_pr_by_way[0];

        // way 1 can dep on way 0:
        // A RAW
        if (dest_write_valid_by_way[0] & (dest_ar6_by_way[0] == A_ar6_by_way[1])) begin
            A_pr_by_way[1] = dest_new_pr_by_way[0];
        end else begin
            A_pr_by_way[1] = read_A_pr_by_way[1];
        end
        // B RAW
        if (dest_write_valid_by_way[0] & (dest_ar6_by_way[0] == B_ar6_by_way[1])) begin
            B_pr_by_way[1] = dest_new_pr_by_way[0];
        end else begin
            B_pr_by_way[1] = read_B_pr_by_way[1];
        end
        // C RAW
        if (dest_write_valid_by_way[0] & (dest_ar6_by_way[0] == {1'b1, C_far_by_way[1]})) begin
            C_pr_by_way[1] = dest_new_pr_by_way[0];
        end else begin
            C_pr_by_way[1] = read_C_pr_by_way[1];
        end
        // dest WAW
        if (dest_write_valid_by_way[0] & (dest_ar6_by_way[0] == dest_ar6_by_way[1])) begin
            dest_old_pr_by_way[1] = dest_new_pr_by_way[0];
        end else begin
            dest_old_pr_by_way[1] = read_dest_old_pr_by_way[1];
        end

        // way 2 can dep on ways 1, 0:
        // A RAW
        if (dest_write_valid_by_way[1] & (dest_ar6_by_way[1] == A_ar6_by_way[2])) begin
            A_pr_by_way[2] = dest_new_pr_by_way[1];
        end else if (dest_write_valid_by_way[0] & (dest_ar6_by_way[0] == A_ar6_by_way[2])) begin
            A_pr_by_way[2] = dest_new_pr_by_way[0];
        end else begin
            A_pr_by_way[2] = read_A_pr_by_way[2];
        end
        // B RAW
        if (dest_write_valid_by_way[1] & (dest_ar6_by_way[1] == B_ar6_by_way[2])) begin
            B_pr_by_way[2] = dest_new_pr_by_way[1];
        end else if (dest_write_valid_by_way[0] & (dest_ar6_by_way[0] == B_ar6_by_way[2])) begin
            B_pr_by_way[2] = dest_new_pr_by_way[0];
        end else begin
            B_pr_by_way[2] = read_B_pr_by_way[2];
        end
        // C RAW
        if (dest_write_valid_by_way[1] & (dest_ar6_by_way[1] == {1'b1, C_far_by_way[2]})) begin
            C_pr_by_way[2] = dest_new_pr_by_way[1];
        end else if (dest_write_valid_by_way[0] & (dest_ar6_by_way[0] == {1'b1, C_far_by_way[2]})) begin
            C_pr_by_way[2] = dest_new_pr_by_way[0];
        end else begin
            C_pr_by_way[2] = read_C_pr_by_way[2];
        end
        // dest WAW
        if (dest_write_valid_by_way[1] & (dest_ar6_by_way[1] == dest_ar6_by_way[2])) begin
            dest_old_pr_by_way[2] = dest_new_pr_by_way[1];
        end else if (dest_write_valid_by_way[0] & (dest_ar6_by_way[0] == dest_ar6_by_way[2])) begin
            dest_old_pr_by_way[2] = dest_new_pr_by_way[0];
        end else begin
            dest_old_pr_by_way[2] = read_dest_old_pr_by_way[2];
        end

        // way 3 can dep on ways 2, 1, 0:
        // A RAW
        if (dest_write_valid_by_way[2] & (dest_ar6_by_way[2] == A_ar6_by_way[3])) begin
            A_pr_by_way[3] = dest_new_pr_by_way[2];
        end else if (dest_write_valid_by_way[1] & (dest_ar6_by_way[1] == A_ar6_by_way[3])) begin
            A_pr_by_way[3] = dest_new_pr_by_way[1];
        end else if (dest_write_valid_by_way[0] & (dest_ar6_by_way[0] == A_ar6_by_way[3])) begin
            A_pr_by_way[3] = dest_new_pr_by_way[0];
        end else begin
            A_pr_by_way[3] = read_A_pr_by_way[3];
        end
        // B RAW
        if (dest_write_valid_by_way[2] & (dest_ar6_by_way[2] == B_ar6_by_way[3])) begin
            B_pr_by_way[3] = dest_new_pr_by_way[2];
        end else if (dest_write_valid_by_way[1] & (dest_ar6_by_way[1] == B_ar6_by_way[3])) begin
            B_pr_by_way[3] = dest_new_pr_by_way[1];
        end else if (dest_write_valid_by_way[0] & (dest_ar6_by_way[0] == B_ar6_by_way[3])) begin
            B_pr_by_way[3] = dest_new_pr_by_way[0];
        end else begin
            B_pr_by_way[3] = read_B_pr_by_way[3];
        end
        // C RAW
        if (dest_write_valid_by_way[2] & (dest_ar6_by_way[2] == {1'b1, C_far_by_way[3]})) begin
            C_pr_by_way[3] = dest_new_pr_by_way[2];
        end else if (dest_write_valid_by_way[1] & (dest_ar6_by_way[1] == {1'b1, C_far_by_way[3]})) begin
            C_pr_by_way[3] = dest_new_pr_by_way[1];
        end else if (dest_write_valid_by_way[0] & (dest_ar6_by_way[0] == {1'b1, C_far_by_way[3]})) begin
            C_pr_by_way[3] = dest_new_pr_by_way[0];
        end else begin
            C_pr_by_way[3] = read_C_pr_by_way[3];
        end
        // dest WAW
        if (dest_write_valid_by_way[2] & (dest_ar6_by_way[2] == dest_ar6_by_way[3])) begin
            dest_old_pr_by_way[3] = dest_new_pr_by_way[2];
        end else if (dest_write_valid_by_way[1] & (dest_ar6_by_way[1] == dest_ar6_by_way[3])) begin
            dest_old_pr_by_way[3] = dest_new_pr_by_way[1];
        end else if (dest_write_valid_by_way[0] & (dest_ar6_by_way[0] == dest_ar6_by_way[3])) begin
            dest_old_pr_by_way[3] = dest_new_pr_by_way[0];
        end else begin
            dest_old_pr_by_way[3] = read_dest_old_pr_by_way[3];
        end
    end

    // save map table follows current map table so faster and can perform fine-grain rollback within 4-way as needed
    assign save_map_table = map_table;

    // map table FF logic
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            // init: map AR to equivalent value PR
            for (int iar = 0; iar < corep::AR5_COUNT; iar++) begin
                map_table.iar[iar] <= iar;
            end
            for (int far = 0; far < corep::AR5_COUNT; far++) begin
                map_table.far[far] <= far + corep::AR5_COUNT;
            end
        end
        else begin
            if (restore_valid) begin
                map_table <= restore_map_table;
            end
            else begin
                // prioritize higher ways first -> assign lower ways first
                for (int way = 0; way < 4; way++) begin
                    if (dest_write_valid_by_way[way]) begin
                        if (dest_ar6_by_way[way].is_fp) map_table.far[dest_ar6_by_way[way].ar5] <= dest_new_pr_by_way[way];
                        else                            map_table.iar[dest_ar6_by_way[way].ar5] <= dest_new_pr_by_way[way];
                    end
                end
            end
        end
    end

endmodule