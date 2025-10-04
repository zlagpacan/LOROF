# system
- Full System-on-Chip


# Block Diagram
![system](system.png)


# Core Private Modules
Quad-Core, so 4 of each:

- Core Datapath
    - 4-way superscalar
    - out-of-order
- L1 Instruction Cache
    - 8KB
    - 2-way associative
    - 32B block
    - private, per-core
    - coherent
        - receives snoops from L2 Cache
    - {valid, invalid} cache block states
- L1 Instruction TLB
    - 32-entry
    - 2-way associative
    - private, per-core
    - incoherent
        - SFENCE.VMA instruction triggers relevant TLB entry flush
        - inter-processor interrupts used to notify other cores of page table updates
    - {valid, invalid} page table entry states
- L1 Data Cache
    - 8KB
    - 2-way associative
    - 32B block
    - 2x bank
    - private, per-core
    - coherent
        - receives snoops from L2 Cache
    - MOESIF cache block states
    - write-back
    - supports atomics
- L1 Data TLB
    - 32-entry
    - 2-way associative
    - private, per-core
    - incoherent
        - SFENCE.VMA instruction triggers relevant TLB entry flush
        - inter-processor interrupts used to notify other cores of page table updates
    - {valid, invalid} page table entry states
- L2 Cache
    - 32KB
    - 4-way associative
    - 64B block
    - unified instruction + data
    - private, per-core
    - inclusive with L1 Data Cache
    - coherent
        - receives snoops from Bus
        - sends snoops to L1 Instruction Cache
        - sends snoops L1 Data Cache
    - MOESIF cache block states
    - write-back
- L2 TLB
    - 64-entry
    - 2-way associative
    - unified instruction + data
    - private, per-core
    - non-inclusive non-exclusive with L1 Instruction TLB and L1 Data TLB
    - page table walker
    - Accessed/Dirty page table entry updater
    - incoherent
        - SFENCE.VMA instruction triggers relevant TLB entry flush
        - inter-processor interrupts used to notify other cores of page table updates
        - make coherent requests to L2 Cache
    - {valid, invalid} page table entry states


# Shared System Modules
- Bus
    - split-transaction, pipelined
    - MOESIF coherence
        - snoops L2 Caches
    - memory mapping to DRAM or I/O space
    - supports atomics
- L3 Cache
    - 256KB
    - 8-way associative
    - 64B block
    - unified instruction + data
    - shared among cores
    - {clean, dirty, invalid} cache block states
    - write-back
- Memory Controller
    - DDR3 DRAM controller
    - TBD
- Memory-Mapped CSR's
    - timers
    - clock
    - inter-processor interrupts
- DMA
    - TBD
- I/O Bus
    - TBD
- I/O Devices
    - TBD
- PLIC
    - Platform-Level Interrupt Controller
    - TBD
- CLINT
    - Core-Level Interrupt
    - TBD
