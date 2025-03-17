# LOROF
LOROF: Linux-on-RISCV-on-FPGA

Goal is to design, verify, and implement on FPGA a RISC-V RV32IMAC_Zicsr_Zifencei Sv32 Quad-Core Superscalar Out-of-Order CPU, successfully booting and running Linux. 

## Architecture Basics
- for an intro to the computer architecture concepts involved in LOROF, check out [basics](./spec/design/basics/README.md)

## Preliminary Specs
- for specs for RTL modules in the design, check out [modules](./spec/design/modules/README.md)

## System
![system](./spec/design/modules/system/system.png)

- see [system.md](./spec/design/modules/system/system.md) for more info

## Core
![core](./spec/design/modules/core/core.png)

- see [core.md](./spec/design/modules/core/core.md) for more info
