# -------------------------- # 
#  module: alu_pipeline 	 #
#  author: Adam Keith	 	 #
# -------------------------- # 

# --- Design --- #
DUT    = alu_reg_pipeline
DESIGN = ../../source/rtl/$(DUT).sv ../../source/rtl/alu.sv
PKG    = ../../source/include

# --- Testbench/Sim --- #
UVM      = testbench
TEST_MOD = top
QSIM     = /package/eda/mg/questa10.6b/questasim
VCD      = wave.do

# --- OS Commands --- #
UNAME_S := $(shell uname -s)

ifeq ($(UNAME_S), Linux)
	PIP    = pip3
	PYTHON = python3
	CLEAN_CMD = rm -rf
else ifeq ($(UNAME_S), Darwin)
	PIP    = pip3
	PYTHON = python3
	CLEAN_CMD = rm -rf
else ifeq ($(OS), Windows_NT)
	PIP    = pip
	PYTHON = python
	CLEAN_CMD = rmdir /S /Q
else
	$(error Unsupported operating system)
endif


define helpText
-----------------------------------------------------------
Author: Adam Keith
Contributors: 
-----------------------------------------------------------

Overview
-----------------------------------------------------------
Runs all relevant commands for $(DUT) simulation

-----------------------------------------------------------

Targets - run 'make' on any of the below
-----------------------------------------------------------
help:
    display this help text

clean:
    remove QuestaSim generated files/libraries

build:
	build RTL/UVM testbench files

run:
	run the simulation in the command line

debug:
	run the simulation in the GUI
	
-----------------------------------------------------------
endef
export helpText

.PHONY: help
help:
	@echo "$${helpText}"


.PHONY: startup
startup:
	module load /siemens/questa/2021.4


.PHONY: clean
clean:
	$(CLEAN_CMD) work
	$(CLEAN_CMD) transcript
	$(CLEAN_CMD) compile.log
	$(CLEAN_CMD) tr_db.log
	$(CLEAN_CMD) vsim.wlf


.PHONY: build
build:
	vlog -mfcu \
	+incdir+$(DESIGN) \
	+incdir+$(UVM) \
	+incdir+$(PKG) \
	+acc \
	+cover \
	-L $(QSIM)/uvm-1.2 \
	-sv $(DESIGN) \
	$(UVM)/testbench.sv \
	-logfile compile.log


.PHONY: run
run: build
	vsim -c $(TEST_MOD) \
		-L $(QSIM)/uvm-1.2 \
		-voptargs=+acc \
		-coverage \
		+UVM_NO_RELNOTES \
		-do "run -all"


.PHONY: debug
debug: build
	vsim -coverage -i $(TEST_MOD) \
		-L $(QSIM)/uvm-1.2 \
		-voptargs=+acc \
		-coverage \
		+UVM_NO_RELNOTES \
		-do "$(VCD)" \
		-do "run -all"