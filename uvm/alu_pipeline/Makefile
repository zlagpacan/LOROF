# Detect the operating system
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





DUT = alu_pipeline
DESIGN = ../../source/rtl/$(DUT).sv
PKG = ../../source/include


# --- Testbench --- #
UVM = testbench
QSIM = /package/eda/mg/questa10.6b/questasim

define helpText
-----------------------------------------------------------
Author: Adam Keith
Contributors: 
-----------------------------------------------------------

Overview
-----------------------------------------------------------

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
	module load ../../../../siemens/questa/2021.4


.PHONY: clean
clean:
	$(CLEAN_CMD) work


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
	vsim -c top \
		-L $(QSIM)/uvm-1.2 \
		-voptargs=+acc \
		-coverage \
		+UVM_NO_RELNOTES \
		-do "run -all"


.PHONY: debug
debug: build
	vsim -coverage -i top \
		-L $(QSIM)/uvm-1.2 \
		-voptargs=+acc \
		-coverage \
		+UVM_NO_RELNOTES \
		-do "run -all"