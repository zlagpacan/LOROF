`ifndef CORE_TYPES_VH
`define CORE_TYPES_VH

package core_types_pkg;

    parameter XLEN = 32;

    parameter PR_COUNT = 64;
    parameter LOG_PR_COUNT = $clog2(PR_COUNT);
    parameter PRF_BANK_COUNT = 4;
    parameter LOG_PRF_BANK_COUNT = $clog2(PRF_BANK_COUNT);


endpackage

`endif // CORE_TYPES_VH