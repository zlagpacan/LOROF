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

    // rat reads
    input corep::ar6_t [3:0]    A_ar6_by_way,
    output corep::pr_t [3:0]    A_pr_by_way,

    input corep::ar6_t [3:0]    B_ar6_by_way,
    output corep::pr_t [3:0]    B_pr_by_way,

    input corep::ar5_t [3:0]    C_ar5_by_way, // guranteed to be freg
    output corep::pr_t [3:0]    C_pr_by_way,

    // rat writes
    input logic [3:0]           dest_write_valid_by_way,
    input corep::ar6_t [3:0]    dest_ar6_by_way,
    output corep::pr_t [3:0]    dest_old_pr_by_way,
    input corep::pr_t [3:0]     dest_new_pr_by_way,

    // instr yields
    input logic [3:0]   instr_valid_by_way,
    input logic [3:0]   instr_has_freg_by_way, // explicitly differentiate as can have unused fp read from irrelevant bits in instr
    output logic [3:0]  instr_yield_by_way,

    // decode_unit control
    input logic [3:0] perform_rename_by_way, // can do write dep logic early in cycle, this late in cycle; decode_unit takes into account rat's instr_yield

    // checkpoint save
    output corep::rat_t save_irat,
    output corep::rat_t save_frat,

    // checkpoint restore
    input logic         restore_valid,
    input corep::rat_t  restore_irat,
    input corep::rat_t  restore_frat
);

    // ----------------------------------------------------------------
    // Signals:

    // rat arrays
    corep::rat_t irat;
    corep::rat_t frat;

    // rat reads
    corep::pr_t [3:0] read_irat_A_pr_by_way;
    corep::pr_t [3:0] read_irat_B_pr_by_way;
    corep::pr_t [3:0] read_irat_dest_old_pr_by_way;
    
    corep::ar5_t read_frat_A_ar5;
    corep::ar5_t read_frat_B_ar5;
    corep::ar5_t read_frat_C_ar5;
    corep::ar5_t read_frat_dest_ar5;
    
    corep::pr_t read_frat_A_pr;
    corep::pr_t read_frat_B_pr;
    corep::pr_t read_frat_C_pr;
    corep::pr_t read_frat_dest_old_pr;

    logic [3:0] frat_grant_one_hot;
    corep::pr_t frat_grant_dest_new_pr;

    // ----------------------------------------------------------------
    // Logic: 

    // irat reads
    always_comb begin
        for (int way = 0; way < 4; way++) begin
            read_irat_A_pr_by_way[way] = irat[A_ar6_by_way[way].ar5];
            read_irat_B_pr_by_way[way] = irat[B_ar6_by_way[way].ar5];
            read_irat_dest_old_pr_by_way[way] = irat[C_ar5_by_way[way]];
        end
    end
    
    // pmux to choose which way gets frat
    pmux_lsb_for #(
        .SEL_WIDTH(4),
        .DATA_WIDTH($bits({read_frat_A_ar5, read_frat_B_ar5, read_frat_C_ar5, read_frat_dest_ar5, frat_grant_dest_new_pr}))
    ) FRAT_PMUX (
        .req_valid_vec(instr_valid_by_way & instr_has_freg_by_way),
        .req_data_vec({
            {A_ar6_by_way[3].ar5, B_ar6_by_way[3].ar5, C_ar5_by_way[3], dest_ar6_by_way[3].ar5, dest_new_pr_by_way[3]},
            {A_ar6_by_way[2].ar5, B_ar6_by_way[2].ar5, C_ar5_by_way[2], dest_ar6_by_way[2].ar5, dest_new_pr_by_way[2]},
            {A_ar6_by_way[1].ar5, B_ar6_by_way[1].ar5, C_ar5_by_way[1], dest_ar6_by_way[1].ar5, dest_new_pr_by_way[1]},
            {A_ar6_by_way[0].ar5, B_ar6_by_way[0].ar5, C_ar5_by_way[0], dest_ar6_by_way[0].ar5, dest_new_pr_by_way[0]}
        }),
        .resp_valid_vec(frat_grant_one_hot),
        .resp_data({read_frat_A_ar5, read_frat_B_ar5, read_frat_C_ar5, read_frat_dest_ar5, frat_grant_dest_new_pr})
    );

    // frat reads
    always_comb begin
        read_frat_A_pr = frat[read_frat_A_ar5];
        read_frat_B_pr = frat[read_frat_B_ar5];
        read_frat_C_pr = frat[read_frat_C_ar5];
        read_frat_dest_old_pr = frat[read_frat_dest_ar5];
    end

    // bypassing and frat vs. irat select
    always_comb begin
        // always assume this way gets the frat if want freg
            // if did get frat, perfect
            // if instr won't use ireg or freg, no issue
            // if instr didn't get frat, it won't be yielded, fine if pick up garbage freg
            // if instr won't be yielded, fine if pick up garbage freg

        // false deps
            // if instr won't use ireg or freg, no issue
            // if instr didn't get frat, it won't be yielded, fine if pick up garbage bypass
            // if instr won't be yielded, fine if pick up garbage bypass
        
        // no deps for way 0:
        if (A_ar6_by_way[0].is_freg)    A_pr_by_way[0] = read_frat_A_pr;
        else                            A_pr_by_way[0] = read_irat_A_pr_by_way[0];
        if (B_ar6_by_way[0].is_freg)    B_pr_by_way[0] = read_frat_B_pr;
        else                            B_pr_by_way[0] = read_irat_B_pr_by_way[0];
        C_pr_by_way[0] = read_frat_C_pr;
        if (dest_ar6_by_way[0].is_freg) dest_old_pr_by_way[0] = read_frat_dest_old_pr;
        else                            dest_old_pr_by_way[0] = read_irat_dest_old_pr_by_way[0];

        // way 1 can dep on way 0:
        // A RAW
        if (dest_write_valid_by_way[0] & (dest_ar6_by_way[0] == A_ar6_by_way[1])) begin
            A_pr_by_way[1] = dest_new_pr_by_way[0];
        end else begin
            if (A_ar6_by_way[1].is_freg)    A_pr_by_way[1] = read_frat_A_pr;
            else                            A_pr_by_way[1] = read_irat_A_pr_by_way[1];
        end
        // B RAW
        if (dest_write_valid_by_way[0] & (dest_ar6_by_way[0] == B_ar6_by_way[1])) begin
            B_pr_by_way[1] = dest_new_pr_by_way[0];
        end else begin
            if (B_ar6_by_way[1].is_freg)    B_pr_by_way[1] = read_frat_B_pr;
            else                            B_pr_by_way[1] = read_irat_B_pr_by_way[1];
        end
        // C RAW (bypass impossible as would mean multiple instr_has_freg_by_way)
        C_pr_by_way[1] = read_frat_C_pr;
        // dest WAW
        if (dest_write_valid_by_way[0] & (dest_ar6_by_way[0] == dest_ar6_by_way[1])) begin
            dest_old_pr_by_way[1] = dest_new_pr_by_way[0];
        end else begin
            if (dest_ar6_by_way[1].is_freg) dest_old_pr_by_way[1] = read_frat_dest_old_pr;
            else                            dest_old_pr_by_way[1] = read_irat_dest_old_pr_by_way[1];
        end

        // way 2 can dep on ways 1, 0:
        // A RAW
        if (dest_write_valid_by_way[1] & (dest_ar6_by_way[1] == A_ar6_by_way[2])) begin
            A_pr_by_way[2] = dest_new_pr_by_way[1];
        end else if (dest_write_valid_by_way[0] & (dest_ar6_by_way[0] == A_ar6_by_way[2])) begin
            A_pr_by_way[2] = dest_new_pr_by_way[0];
        end else begin
            if (A_ar6_by_way[2].is_freg)    A_pr_by_way[2] = read_frat_A_pr;
            else                            A_pr_by_way[2] = read_irat_A_pr_by_way[2];
        end
        // B RAW
        if (dest_write_valid_by_way[1] & (dest_ar6_by_way[1] == B_ar6_by_way[2])) begin
            B_pr_by_way[2] = dest_new_pr_by_way[1];
        end else if (dest_write_valid_by_way[0] & (dest_ar6_by_way[0] == B_ar6_by_way[2])) begin
            B_pr_by_way[2] = dest_new_pr_by_way[0];
        end else begin
            if (B_ar6_by_way[2].is_freg)    B_pr_by_way[2] = read_frat_B_pr;
            else                            B_pr_by_way[2] = read_irat_B_pr_by_way[2];
        end
        // C RAW (bypass impossible as would mean multiple instr_has_freg_by_way)
        C_pr_by_way[2] = read_frat_C_pr;
        // dest WAW
        if (dest_write_valid_by_way[1] & (dest_ar6_by_way[1] == dest_ar6_by_way[2])) begin
            dest_old_pr_by_way[2] = dest_new_pr_by_way[1];
        end else if (dest_write_valid_by_way[0] & (dest_ar6_by_way[0] == dest_ar6_by_way[2])) begin
            dest_old_pr_by_way[2] = dest_new_pr_by_way[0];
        end else begin
            if (dest_ar6_by_way[2].is_freg) dest_old_pr_by_way[2] = read_frat_dest_old_pr;
            else                            dest_old_pr_by_way[2] = read_irat_dest_old_pr_by_way[2];
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
            if (A_ar6_by_way[3].is_freg)    A_pr_by_way[3] = read_frat_A_pr;
            else                            A_pr_by_way[3] = read_irat_A_pr_by_way[3];
        end
        // B RAW
        if (dest_write_valid_by_way[2] & (dest_ar6_by_way[2] == B_ar6_by_way[3])) begin
            B_pr_by_way[3] = dest_new_pr_by_way[2];
        end else if (dest_write_valid_by_way[1] & (dest_ar6_by_way[1] == B_ar6_by_way[3])) begin
            B_pr_by_way[3] = dest_new_pr_by_way[1];
        end else if (dest_write_valid_by_way[0] & (dest_ar6_by_way[0] == B_ar6_by_way[3])) begin
            B_pr_by_way[3] = dest_new_pr_by_way[0];
        end else begin
            if (B_ar6_by_way[3].is_freg)    B_pr_by_way[3] = read_frat_B_pr;
            else                            B_pr_by_way[3] = read_irat_B_pr_by_way[3];
        end
        // C RAW (bypass impossible as would mean multiple instr_has_freg_by_way)
        C_pr_by_way[3] = read_frat_C_pr;
        // dest WAW
        if (dest_write_valid_by_way[2] & (dest_ar6_by_way[2] == dest_ar6_by_way[3])) begin
            dest_old_pr_by_way[3] = dest_new_pr_by_way[2];
        end else if (dest_write_valid_by_way[1] & (dest_ar6_by_way[1] == dest_ar6_by_way[3])) begin
            dest_old_pr_by_way[3] = dest_new_pr_by_way[1];
        end else if (dest_write_valid_by_way[0] & (dest_ar6_by_way[0] == dest_ar6_by_way[3])) begin
            dest_old_pr_by_way[3] = dest_new_pr_by_way[0];
        end else begin
            if (dest_ar6_by_way[3].is_freg) dest_old_pr_by_way[3] = read_frat_dest_old_pr;
            else                            dest_old_pr_by_way[3] = read_irat_dest_old_pr_by_way[3];
        end
    end

    // yield logic
    always_comb begin
        case (instr_valid_by_way & instr_has_freg_by_way)
            4'b0000, 4'b0001, 4'b0010, 4'b0100, 4'b1000:    instr_yield_by_way = 4'b1111;
            4'b0011, 4'b0111, 4'b1011, 4'b1111:             instr_yield_by_way = 4'b0001;
            4'b0101, 4'b1101, 4'b0110, 4'b1110:             instr_yield_by_way = 4'b0011;
            4'b1001, 4'b1010, 4'b1100:                      instr_yield_by_way = 4'b0111;
        endcase
    end

    // save map table follows current map table so faster and can perform fine-grain rollback within 4-way as needed
    assign save_irat = irat;
    assign save_frat = frat;

    // rat FF logic
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

            // init: map iar's to first 32 pr's
            for (int iar5 = 0; iar5 < corep::AR5_COUNT; iar5++) begin
                irat[iar5] <= iar5;
            end

            // init: map far's to second 32 pr's
            for (int far5 = 0; far5 < corep::AR5_COUNT; far5++) begin
                frat[far5] <= corep::AR5_COUNT + far5;
            end
        end
        else begin
            // restore takes priority
            if (restore_valid) begin
                irat <= restore_irat;
                frat <= restore_frat;
            end
            else begin

                // irat writes
                    // prioritize higher ways first -> assign lower ways first
                for (int way = 0; way < 4; way++) begin
                    if (
                        perform_rename_by_way[way]
                        & dest_write_valid_by_way[way]
                        & ~dest_ar6_by_way[way].is_freg
                    ) begin
                        irat[dest_ar6_by_way[way].ar5] <= dest_new_pr_by_way[way];
                    end
                end

                // frat writes
                    // check if did perform_rename on any instr writing to ar6.is_freg
                if (
                    perform_rename_by_way[0] & dest_write_valid_by_way[0] & dest_ar6_by_way[0].is_freg
                    | perform_rename_by_way[1] & dest_write_valid_by_way[1] & dest_ar6_by_way[1].is_freg
                    | perform_rename_by_way[2] & dest_write_valid_by_way[2] & dest_ar6_by_way[2].is_freg
                    | perform_rename_by_way[3] & dest_write_valid_by_way[3] & dest_ar6_by_way[3].is_freg
                ) begin
                    frat[read_frat_dest_ar5] <= frat_grant_dest_new_pr;
                end
            end
        end
    end

endmodule