module istream_marker (
    input logic [15:0] valid_vec,
    input logic [15:0] uncompressed_vec,
    output logic [15:0] marker_vec
);

    always_comb begin

        // marker vec
        marker_vec[0] = valid_vec[0];
        for (int i = 1; i <= 14; i++) begin
            marker_vec[i] = valid_vec[i] & ~(marker_vec[i-1] & uncompressed_vec[i-1]);
        end
        marker_vec[15] = valid_vec[15] & ~uncompressed_vec[15] & ~(marker_vec[14] & uncompressed_vec[14]);
    end

endmodule