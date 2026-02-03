/*
    Filename: ibuffer_deqer.sv
    Author: zlagpacan
    Description: RTL for Instruction Buffer Dequeuer
    Spec: LOROF/spec/design/ibuffer_deqer.md
*/

module ibuffer_deqer (

    input logic [15:0]          valid_vec,
    input logic [15:0]          uncompressed_vec,
    input logic [15:0]          redirect_vec,

    output logic [15:0][4:0]    count_vec,
    output logic [15:0]         deqing_vec,

    output logic [3:0]          valid_by_way,
    output logic [3:0][3:0]     first_idx_by_way,
    output logic [3:0][3:0]     second_idx_by_way
);

    // ----------------------------------------------------------------
    // Signals:

    logic [15:0] count_up_vec;

    logic [3:0][15:0] mask_by_way;

    // ----------------------------------------------------------------
    // Logic:

    always_comb begin
        // special case first entry
        count_up_vec[0] = valid_vec[0];

        // general case
        for (int i = 1; i <= 6; i++) begin
            count_up_vec[i] = valid_vec[i] & (~count_up_vec[i-1] | ~uncompressed_vec[i-1]);
        end

        // special case at shift reg boundary -> can only be uncompressed if [8] valid or redirect
        count_up_vec[7] = valid_vec[7] & (~uncompressed_vec[7] | valid_vec[8] | redirect_vec[7]) & (~count_up_vec[6] | ~uncompressed_vec[6]);

        // general case
        for (int i = 8; i <= 14; i++) begin
            count_up_vec[i] = valid_vec[i] & (~count_up_vec[i-1] | ~uncompressed_vec[i-1]);
        end

        // special case last entry -> can only be uncompressed if redirect
        count_up_vec[15] = valid_vec[15] & (~uncompressed_vec[15] | redirect_vec[15]) & (~count_up_vec[14] | ~uncompressed_vec[14]);

        // apply count up
        count_vec[0] = count_up_vec[0];
        for (int i = 1; i <= 15; i++) begin
            count_vec[i] = count_vec[i-1] + count_up_vec[i];
        end
    end

    always_comb begin
        for (int i = 0; i <= 15; i++) begin
            if (count_vec[i] <= 4) begin
                deqing_vec[i] = 1'b1;
            end
            else begin
                deqing_vec[i] = 1'b0;
            end
        end
    end

    genvar way;
    generate
        for (way = 0; way < 4; way++) begin
            always_comb begin
                for (int i = 0; i <= 15; i++) begin
                    mask_by_way[way][i] = (count_vec[i] == (way + 1));
                end
            end
            pe_lsb_tree #(
                .WIDTH(16)
            ) FIRST_PE_LSB_BY_WAY (
                .req_vec(mask_by_way[way]),
                .ack_valid(valid_by_way[way]),
                .ack_index(first_idx_by_way[way])
            );
            // can guarantee second priority by way will be exact next bit after first,
            // so can just do pe on shifted vec
            pe_lsb_tree #(
                .WIDTH(16)
            ) SECOND_PE_LSB_BY_WAY (
                .req_vec(mask_by_way[way] << 1),
                .ack_valid(),
                .ack_index(second_idx_by_way[way])
            );
        end
    endgenerate

endmodule