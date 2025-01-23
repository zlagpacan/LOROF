SBY_PATH := ../../../../../Downloads/oss-cad-suite/environment
SBY_EXEC = progctr.sby

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
	- contains Symbiyosys demo

- Makefile
    - runs necessary commands
-----------------------------------------------------------

Targets - run 'make' on any of the below
-----------------------------------------------------------
help:
    display this help text

clean:
    remove generated sby files

startup:
    set environment path

run:
	runs sby exec set in makefile

-----------------------------------------------------------
endef
export helpText

.PHONY: help
help:
	@echo "$${helpText}"

# TODO: add error ignore option
.PHONY: clean
clean:
	@find . -type d -name 'progctr*' -exec $(CLEAN_CMD) {} +


# FIXME: Broken - just run source and copy paste machines path to SBY_PATH above
.PHONY: startup
startup:
	source $(SBY_PATH)

.PHONY: run
run:
	sby -f $(SBY_EXEC)
	

