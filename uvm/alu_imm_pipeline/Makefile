# ********************************************************** #
#  Author      : Adam Keith                                  #
#  Description : alu_imm_pipeline Makefile                   #
# ********************************************************** #
include ../Makefile.inc

# --- Design --- #
DUT      = alu_imm_pipeline
DESIGN   = ../../source/rtl/$(DUT).sv
PKG      = ../../source/include
RTL_DEPS = ../../source/rtl/alu.sv

# --- Testbench/Sim --- #
UVM_DIR  = testbench
TB_FILE  = testbench/testbench.sv
TEST_MOD = top
QSIM_ENV = /package/eda/mg/questa2021.4/questasim
VCD      = wave.do
SVA      = $(UVM_DIR)/assertions/$(DUT)_sva.sv

# --- Tools --- #
RESULTS_SCRIPT_DIR = ../../tools/uvm_results
PARSE_RESULTS      = $(RESULTS_SCRIPT_DIR)/parse_results.py
TRANSCRIPT         = transcript
UVM_REPORT         = results.rpt
RPT                = 1
