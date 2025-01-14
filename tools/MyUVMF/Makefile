EXEC := generate.py
SPEC := demo/alu.yaml

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

define helpText
-----------------------------------------------------------
Author: Adam Keith
Contributors: 
-----------------------------------------------------------

Overview
-----------------------------------------------------------
> demo
    - contains spec for ALU demo

> jinja
    - houses jinja2 templates

> testbench (generated)
    - houses generated UVM files

- conifg.yaml
    - YAML spec for DUT and UVM features

- generate.py
    - main process for generating UVM files

- lib.py
    - houses helper functions for generate.py

- Makefile
    - runs necessary commands
-----------------------------------------------------------

Targets - run 'make' on any of the below
-----------------------------------------------------------
help:
    display this help text

clean:
    remove generated testbench

startup:
    install dependencies

run:
    runs make clean
    runs generate.py to generate UVM files and place
        in the 'testbench' directory
-----------------------------------------------------------
endef
export helpText

.PHONY: help
help:
	@echo "$${helpText}"

.PHONY: clean
clean:
	$(CLEAN_CMD) testbench

.PHONY: startup
startup:
	$(PIP) install pyyaml
	$(PIP) install jinja2

.PHONY: run
run: startup
	make clean

	@echo "Creating test-bench directory..."
	mkdir testbench
	@echo $${runText}
	$(PYTHON) "${EXEC}" $(SPEC)
