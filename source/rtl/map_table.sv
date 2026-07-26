/*
    Filename: map_table.sv
    Author: zlagpacan
    Description: RTL for Architectural to Physical Register Map Table
    Spec: LOROF/spec/design/map_table.md
*/

`include "corep.vh"

module map_table #(
    // hardcode 4-way
) (
    // seq
    input logic CLK,
    input logic nRST,

    // reg reads
    input corep::ar6_t [3:0]    A_ar6_by_way,
    output corep::pr_t [3:0]    A_pr_by_way,

    input corep::ar6_t [3:0]    B_ar6_by_way,
    output corep::pr_t [3:0]    B_pr_by_way,

    input corep::ar5_t [3:0]    C_far_by_way,
    output corep::pr_t [3:0]    C_pr_by_way,

    // reg writes
    input logic [3:0]           dest_write_valid_by_way,
    input corep::ar6_t [3:0]    dest_ar6_by_way,
    output corep::pr_t [3:0]    dest_old_pr_by_way,
    input corep::pr_t [3:0]     dest_new_pr_by_way,

    // checkpoint save
    output corep::map_table_t   save_map_table,

    // checkpoint restore
    input logic                 restore_valid,
    input corep::map_table_t    restore_map_table
);

    // ----------------------------------------------------------------
    // Signals:

    // map table FF array
    corep::map_table_t map_table;

    // map table read values
    corep::pr_t [3:0] read_A_pr_by_way;
    corep::pr_t [3:0] read_B_pr_by_way;
    corep::pr_t [3:0] read_C_pr_by_way;
    corep::pr_t [3:0] read_dest_old_pr_by_way;

    // ----------------------------------------------------------------
    // Logic: 

    // map table reads
    always_comb begin
        for (int way = 0; way < 4; way++) begin

            if (A_ar6_by_way[way].is_fp) begin
                read_A_pr_by_way[way] = map_table.far[A_ar6_by_way[way].ar5];
            end else begin
                read_A_pr_by_way[way] = map_table.iar[A_ar6_by_way[way].ar5];
            end

            if (B_ar6_by_way[way].is_fp) begin
                read_B_pr_by_way[way] = map_table.far[B_ar6_by_way[way].ar5];
            end else begin
                read_B_pr_by_way[way] = map_table.iar[B_ar6_by_way[way].ar5];
            end

            read_C_pr_by_way[way] = map_table.far[C_far_by_way[way]];

            if (dest_ar6_by_way[way].is_fp) begin
                read_dest_old_pr_by_way[way] = map_table.far[dest_ar6_by_way[way].ar5];
            end else begin
                read_dest_old_pr_by_way[way] = map_table.iar[dest_ar6_by_way[way].ar5];
            end
        end
    end

    // map table bypassing
    always_comb begin
        
        // no deps for way 0:
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