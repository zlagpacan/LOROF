`include "core_types_pkg.vh"
import core_types_pkg::*;

module prf_ff (

    // seq
    input logic CLK,
    input logic nRST,

    // read req info by read requester
    input logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0]    read_req_PR_by_rr,

    // read resp info by read requestor
    output logic [PRF_RR_COUNT-1:0][31:0]     read_resp_data_by_rr,

    // writeback info by write requestor
    input logic [PRF_WR_COUNT-1:0]                          WB_valid_by_wr,
    input logic [PRF_WR_COUNT-1:0][31:0]                    WB_data_by_wr,
    input logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-1:0]        WB_PR_by_wr
);

    // // prf array
    // logic [PR_COUNT-1:0][31:0] prf_array;

    // always_comb begin

    //     for (int rr = 0; rr < PRF_RR_COUNT; rr++) begin
    //         read_resp_data_by_rr[rr] = prf_array[read_req_PR_by_rr[rr]];
    //     end
    // end

    // always_ff @ (posedge CLK, negedge nRST) begin
    //     if (~nRST) begin
    //         prf_array <= '0;
    //     end
    //     else begin
    //         for (int wr = 0; wr < PRF_WR_COUNT; wr++) begin
    //             if (WB_valid_by_wr[wr] & WB_PR_by_wr[wr] != 0) begin
    //                 prf_array[WB_PR_by_wr[wr]] <= WB_data_by_wr[wr];
    //             end
    //         end
    //     end
    // end

    // prf array by rr
    logic [PRF_RR_COUNT-1:0][PR_COUNT-1:0][31:0] prf_array_by_rr;

    always_comb begin

        for (int rr = 0; rr < PRF_RR_COUNT; rr++) begin
            read_resp_data_by_rr[rr] = prf_array_by_rr[rr][read_req_PR_by_rr[rr]];
        end
    end

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            prf_array <= '0;
        end
        else begin
            for (int wr = 0; wr < PRF_WR_COUNT; wr++) begin
                if (WB_valid_by_wr[wr] & WB_PR_by_wr[wr] != 0) begin
                    for (int rr = 0; rr < PRF_RR_COUNT; rr++) begin
                        prf_array_by_rr[rr][WB_PR_by_wr[wr]] <= WB_data_by_wr[wr];
                    end
                end
            end
        end
    end

endmodule