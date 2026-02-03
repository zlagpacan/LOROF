/*
    Filename: ibuffer_deqer.sv
    Author: zlagpacan
    Description: RTL for Instruction Buffer Dequeuer
    Spec: LOROF/spec/design/ibuffer_deqer.md
*/

module ibuffer_deqer (

    input logic [15:0]          valid_vec,
    input logic [15:0]          uncompressed_vec,

    output logic [15:0][4:0]    count_vec,
    output logic [15:0]         deqing_vec,

    output logic [3:0]          valid_by_way,
    output logic [3:0][3:0]     first_index_by_way,
    output logic [3:0][3:0]     second_index_by_way
);

    // ----------------------------------------------------------------
    // Signals:

    logic [15:0] count_up_vec;

    logic [3:0][15:0] mask_by_way;

    // ----------------------------------------------------------------
    // Logic:

    always_comb begin
        count_up_vec[0] = valid_vec[0];
        for (int i = 1; i <= 14; i++) begin
            count_up_vec[i] = valid_vec[i] & (~count_up_vec[i-1] | ~uncompressed_vec[i-1]);
        end
        count_up_vec[15] = valid_vec[15] & ~uncompressed_vec[15] & (~count_up_vec[14] | ~uncompressed_vec[14]);

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
                .ack_index(first_index_by_way[way])
            );
            pe_lsb_tree #(
                .WIDTH(16)
            ) SECOND_PE_LSB_BY_WAY (
                .req_vec(mask_by_way[way] << 1),
                .ack_valid(),
                .ack_index(second_index_by_way[way])
            );
        end
    endgenerate

endmodule