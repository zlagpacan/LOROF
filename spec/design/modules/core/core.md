# core
- CPU Core Datapath
    - see [core_basics.md](../../basics/core_basics.md) for basic core architecture concepts


# Block Diagram
![core](core.png)


# Frontend
- 4-way superscalar in typical and ideal circumstances
- 16B instruction fetch per cycle
- 4x instruction dispatch per cycle
- C-extension support
    - can execute 2B and 4B instructions
- minimum 5-cycle latency from instruction fetch start to dispatch

## Fetch and Prediction Modules
- Program Counter (PC)
    - Instruction Cache and prediction read index
    - 16B aligned granularity + masking of unwanted instruction bytes
- Branch Target Buffer (BTB)
    - lower branch target bits by PC, ASID
    - also holds tags for associativity
    - also holds branch prediction info
        - if jump, if link, if return, prediction accuracy, 2-bit counter vs. LBPT vs. GBPT selection, UPCT index
    - associated with each 2B of 16B instruction fetch
        - 8-entry read per cycle
    - 2048-entry
    - 2-way associative
- Local History Table (LHT)
    - local branch history by PC, ASID
    - associated with each 2B of 16B instruction fetch
        - 8-entry read per cycle
    - 8-bit history
    - 256-entry
    - direct-mapped
- Memory Dependence Prediction Table (MDPT)
    - 2-bit prediction that load is vs. isn't dependent on data in STAMOU
    - associated with each 2B of 16B instruction fetch
        - 8-entry read per cycle
    - 4096-entry
    - direct-mapped
- Local Branch Prediction Table (LBPT)
    - 2-bit counter branch prediction by local history, PC, ASID
    - get 1-cycle bubble if use
    - 256-entry
    - direct-mapped
- Global History Register (GHR)
    - history of all previous branch taken vs. not taken
    - 12-bit history
- Global Branch Prediction Table (GBPT)
    - 2-bit counter branch prediction by global history, PC, ASID
    - get 1-cycle bubble if use
    - 4096-entry
    - direct-mapped
- Upper PC Table (UPCT)
    - small table of upper target address PC bits
    - 8-entry
    - associative PLRU replacement on update
- Return Address Stack (RAS)
    - LIFO array of return address PC's
    - responds to predicted links and returns
    - 8-entry
- Prediction Logic
    - select relevant actions based on total 16B instruction prediction info
- Updater
    - update prediction tables when given branch notifications from ROB
    - non-trivial due to read-modify-write nature and interdependence between update information among tables
- Instruction TLB
- Instruction Cache

## Decode Modules
- Instruction Stream (iStream)
    - enqueue arbitrarily-2B-aligned set of 16 instruction bytes
    - dequeue 4x aligned instructions
    - 8x 16B-wide entries
- Decoder
    - 4-way superscalar instruction decoder
    - also check for accidental branch prediction of non-branch instructions or missing instruction bytes
        - need to restart Frontend after such an instruction
- Free List
    - FIFO list of registers available for rename
    - 4-way superscalar free physical register enqueue and dequeue
- Map Table
    - table mapping architectural register to physical register
    - 12x read ports, 4x write ports
        - 4x instructions with 2x source operand reads and 1x dest operand read
            - need to read previous dest operand for eventual physical register freeing
        - 4x instructions with 1x dest operand write
- Architectural Register Dependence Checker
    - check for relevant register RAW, WAR, and WAW hazards so the correct physical registers are used by the instructions and updated in the map table
- Checkpoint Array
    - array of checkpointed Map Tables
    - use to allow fast restart of Frontend using a checkpoint of architectural state
    - also saves branch local history, global history, and RAS index
- Ready Table
    - table mapping physical register to its {ready, not ready} state


# Backend
- 7-way superscalar in ideal circumstances

## 7x Pipelines
- ALU Register-Register Pipeline
    - 3-stage pipeline
    - collect register operands
    - perform ALU op
    - send register write to PRF
- ALU Register-Immediate Pipeline
    - 3-stage pipeline
    - collect register operand
    - perform ALU op
    - send register write to PRF
- Multiplication-Division Unit (MDU) Pipeline
    - TBD stages
    - collect register operands
    - perform multiplication or division op
    - send register write to PRF
- Branch Resolution Unit (BRU) Pipeline
    - 4-stage pipeline
    - collect register operands
    - calculate branch targets and register write values
    - send register write to PRF
    - send restart request to ROB if branch is determined to be mispredicted
- Load Unit (LDU) Pipeline + Queue
    - TBD stages
    - collect load address register operand
    - calculate load address
    - perform load: read dcache
    - check STAMOU for dependent store or AMO
        - potentially forward value to load
        - potentially send restart request to ROB if dependent store or AMO was discovered after load value returned from dcache
- Store + Atomic Memory Operation Unit (STAMOU) Pipeline + Queue
    - TBD stages
    - collect store/AMO address and data register operands
    - calculate store/AMO address
    - perform store: write dcache
    - perform AMO: read, modify, and write dcache value
        - or send AMO to bus
    - provide info for loads to check for dependent values
- System + CSR (SYS) Pipeline
    - TBD stages
    - collect register operand
    - perform system operation: modify core state
    - perform CSR operation: read, modify, and write CSRF
        - may also modify core state

## 5x Issue Queues (IQs)
- ALU Register-Register + MDU IQ
    - simultaneous 1x out-of-order issue per pipeline
        - 2x issue per cycle if have ALU Reg-Reg and MDU ready op
    - 8x entry
- BRU IQ
    - 1x out-of-order issue
        - 1x issue per cycle
    - 4x entry
- ALU Register-Immediate + LDU IQ
    - simultaneous 1x out-of-order issue per pipeline
        - 2x issue per cycle if have ALU Reg-Imm and LDU ready op
    - 8x entry
- STAMOU IQ
    - 1x in-order issue
        - 1x issue per cycle if oldest STAMOU op is ready
    - 16x entry
- SYS IQ
    - in-order issue
        - 1x issue per cycle if oldest SYS op is ready
    - 4x entry

## Architectural State Modules
- Physical Register File (PRF)
    - 128x 32-bit physical registers
    - 4x banks
        - 2 read ports each
        - 1 write port each
    - ideally 8x reads and 4x writes per cycle
- Control-Status Register File (CSRF)
    - array of CSR's
    - TBD
- Data TLB
- Data Cache

# Reorder Buffer (ROB)
- receive instructions dispatched in-order
    - 4x instruction enqueue per cycle
- receive completion notifications out-of-order 
- receive restart requests out-of-order
    - potentially restart Frontend
- receive branch notifications out-or-order
    - potentially udpate Frontend prediction tables
- ensure architectural state is correctly modified, appearing in-order
    - 4x instruction dequeue per cycle
- 128x entry
    - 32x 4-wide entries