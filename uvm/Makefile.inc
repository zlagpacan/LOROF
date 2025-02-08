# ********************************************************** #
#  Author      : Adam Keith                                  #
#  Description : include for UVM simulations                 #
# ********************************************************** #

# --- Design --- #
DUT      ?= 
DESIGN   ?= ../../source/rtl/$(DUT).sv
PKG      ?= ../../source/include
RTL_DEPS ?= 

# --- Testbench/Sim --- #
UVM_DIR  ?= testbench
TB_FILE  ?= testbench.sv
TEST_MOD ?= top
QSIM_ENV ?= /package/eda/mg/questa10.6b/questasim
VCD      ?= wave.do
SVA      ?= $(UVM_DIR)/assertions/$(DUT)_sva.sv

# --- Tools --- #
RESULTS_SCRIPT_DIR ?= ../../tools/uvm_results
PARSE_RESULTS      ?= $(RESULTS_SCRIPT_DIR)/parse_results.py
TRANSCRIPT         ?= transcript
UVM_REPORT         ?= results.rpt
RPT                ?= 1

# --- OS Commands --- #
UNAME_S := $(shell uname -s)

ifeq ($(UNAME_S), Linux)
	PIP       = pip3
	PYTHON    = python3
	CLEAN_CMD = rm -rf
else ifeq ($(UNAME_S), Darwin)
	PIP       = pip3
	PYTHON    = python3
	CLEAN_CMD = rm -rf
else ifeq ($(OS), Windows_NT)
	PIP       = pip
	PYTHON    = python
	CLEAN_CMD = rmdir /S /Q
else
	$(error Unsupported operating system)
endif


define helpText
-----------------------------------------------------------
Author:       Adam Keith
Contributors: NA


Overview
-----------------------------------------------------------
Runs all relevant commands for $(DUT) simulation.


Targets - run 'make' on any of the below
-----------------------------------------------------------
help:   display this help text
clean:  remove QuestaSim generated files/libraries
build:  build RTL/UVM testbench files
run:    run the simulation in the command line
    	set RPT=0 to turn off results reporting
debug:  run the simulation in the GUI
all:    clean compile run report
report: testcase report
	
-----------------------------------------------------------
endef
export helpText

.PHONY: help
help:
	@echo "$${helpText}"

# FIXME: Doesn't work
.PHONY: startup
startup:
	module load siemens/questa/2021.4

# Remove QuestaSim generated libraries/reports
.PHONY: clean
clean:
	$(CLEAN_CMD) work
	$(CLEAN_CMD) transcript
	$(CLEAN_CMD) compile.log
	$(CLEAN_CMD) tr_db.log
	$(CLEAN_CMD) vsim.wlf
	$(CLEAN_CMD) coverage.rpt

# Compile testbench/rtl
.PHONY: build
build:
	vlog -mfcu \
        +incdir+$(DESIGN) \
        +incdir+$(RTL_DEPS) \
        +incdir+$(UVM) \
        +incdir+$(PKG) \
        +acc \
        +cover \
        -L $(QSIM_ENV)/uvm-1.2 \
        -sv $(DESIGN) \
		-sv $(RTL_DEPS) \
        -sv $(TB_FILE) \
        -sv $(SVA) \
        -logfile compile.log

# Run simulation in the command line
.PHONY: run
run: build
	vsim -c $(TEST_MOD) \
		-L $(QSIM_ENV)/uvm-1.2 \
		-voptargs=+acc \
		-coverage \
		+UVM_NO_RELNOTES \
		-do "run -all"

ifeq ($(RPT), 1)
	make report
endif

# Run simulation in the GUI
.PHONY: debug
debug: build
	vsim -coverage -i $(TEST_MOD) \
		-L $(QSIM_ENV)/uvm-1.2 \
		-voptargs=+acc \
		-coverage \
		+UVM_NO_RELNOTES \
		-do "$(VCD)" \
		-do "run -all"
	
#vsim -do "coverage report -detail -cvg -directive -comments -output coverage.rpt /."
	
# Clean compile and build testbench
.PHONY: all
all: clean build run

# Generate report based on QuestaSim transcript
.PHONY: report
report:
	$(PYTHON) "$(PARSE_RESULTS)" $(TRANSCRIPT) $(UVM_REPORT)

.PHONY: coverage_rpt
coverage_rpt:
	cp coverage.rpt cov_results.rpt
