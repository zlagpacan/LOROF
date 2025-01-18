`ifndef CORE_TYPES_VH
`define CORE_TYPES_VH

package core_types_pkg;

    // general
    parameter XLEN = 32;

    // PRF
    parameter PR_COUNT = 128;
    parameter LOG_PR_COUNT = $clog2(PR_COUNT);
    parameter PRF_BANK_COUNT = 4;
    parameter LOG_PRF_BANK_COUNT = $clog2(PRF_BANK_COUNT);
    parameter PRF_RR_COUNT = 14;    // read requestor count
    parameter PRF_READ_PORT_COUNT = 2;
    parameter PRF_WR_COUNT = 7;     // write requestor count

    // ROB
    parameter ROB_ENTRIES = 128;
    parameter LOG_ROB_ENTRIES = $clog2(ROB_ENTRIES);

    // // DQ
    // parameter DQ_ENTRIES = 8;
    // parameter LOG_DQ_ENTRIES = $clog2(DQ_ENTRIES);
        // deprecated
        // just increase IQ sizes

    // IQ
    parameter ALU_REG_IQ_ENTRIES = 8;
    parameter ALU_IMM_IQ_ENTRIES = 8;
    parameter BRU_IQ_ENTRIES = 8;
    parameter LQ_IQ_ENTRIES = 8;
    parameter SQ_IQ_ENTRIES = 8;
    parameter AMOQ_IQ_ENTRIES = 4;
    parameter SYS_IQ_ENTRIES = 4;
    parameter MD_IQ_ENTRIES = 4;

endpackage

`endif // CORE_TYPES_VH