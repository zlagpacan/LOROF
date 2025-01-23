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

# --- Design --- #
DESIGN = flist.f

# --- Testbench --- #
UVM = testbench

QSIM = /siemens/questa/2021.4

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
	vlog -mfcu \
	+incdir+$(DESIGN) \
	+incdir+$(UVM) \
	+acc \
	+cover \
	-L $(QSIM)/uvm-1.2 \
	-sv $(DESIGN) \
	-logfile compile.log

run:
	vsim -c $(UVM)/testbench.sv \
		-L TODO: \
		-voptargs=+acc \
		-coverage \
		-do "run -all"

debug:
	vsim -coverage -i $(UVM)/testbench.sv \
		-L TODO: \
		-voptargs=+acc \
		-coverage \
		-do "run -all"

-----------------------------------------------------------
endef
export helpText

.PHONY: help
help:
	@echo "$${helpText}"


.PHONY: clean
clean:
	$(CLEAN_CMD)

.PHONY: build
build:
	vlog -mfcu \
	+incdir+$(DESIGN) \
	+incdir+$(UVM) \
	+acc \
	+cover \
	-L $(QSIM)/uvm-1.2 \
	-sv $(DESIGN) \
	-logfile compile.log


.PHONY: run
run: 
	vsim -c $(UVM)/testbench.sv \
		-L $(QSIM)/uvm-1.2 \
		-voptargs=+acc \
		-coverage \
		-do "run -all"

.PHONY: debug
debug:
	vsim -coverage -i $(UVM)/testbench.sv \
		-L $(QSIM)/uvm-1.2 \
		-voptargs=+acc \
		-coverage \
		-do "run -all"