# CSR List
ISA: RV32IMAC_Zicsr_Zifencei Sv32

- CSR's have associated privilege level where this privelege level and higher privilege levels can access it

## General Rules
- csr[11:0]
    - csr[11:10]
        - 00, 01, 10:
            - read/write
        - 11:
            - read-only
    - csr[9:8]
        - lowest executing privilege level that can access
        - 00:
            - User/Application
            - U-mode
        - 01:
            - Supervisor
            - S-mode
        - 10:
            - reserved
        - 11:
            - Machine
            - M-mode
- raise illegal instruction exception if current privilege level not allowed to access CSR
- raise illegal instruciton exception if try to write to read-only register
    - writes to read-only fields of read/write registers are simply ignored
- dependent CSR's can affect the value of fields of other CSR's if a write to the CSR affects a dependent CSR's field
    - these value modifications do not cause CSR write side affects for the dependent CSR
- implicit CSR reads are equivalent in affect of explicit CSR reads
    - i.e. satp CSR modifications must propagate immediately

### CSR Fields
- WPRI
    - Reserved Writes Preserve Values, Reads Ignore Values
    - SW's job to maintain value if not writing to field
    - if unused: read-only zero
- WLRL
    - Write/Read Only Legal Values
    - only have to support legal values
    - OPTIONAL: raise illegal-instruction exception if SW writes illegal value
    - always read legal values unless wrote illegal value previously
- WARL
    - Write Any Values, Read Legal Values
    - SW can test field to see legal values by trying to write value and see what gets read
    - no exceptions if illegal value
    - always read legal values unless wrote illegal value previously

## Supported CSR's

### Unprivileged CSR's

#### Counters, Timers
- 0xC00: cycle
    - URO
- 0xC01: time
    - URO
- 0xC02: instret
    - instructions retired
    - URO
- 0xC80: cycleh
    - upper 32 bits of cycle
    - URO
- 0xC81: timeh
    - upper 32 bits of time
    - URO
- 0xC82: instreth
    - upper 32 bits of instret
    - URO

### Supervisor CSR's

#### Trap Setup
- 0x100: sstatus
    - supervisor status
    - SRW
- 0x104: sie
    - supervisor interrupt-enable
    - SRW
- 0x105: stvec
    - supervisor trap handler base address
    - SRW
- 0x106: scounteren
    - supervisor counter enable
    - SRW

#### Config
- skip

#### Counter Setup
- 0x120: scountinhibit
    - supervisor sounter-inhibit
    - SRW

#### Trap Handling
- 0x140: sscratch
    - scratch register for supervisor trap handlers
    - SRW
- 0x141: sepc
    - supervisor exception PC
    - SRW
- 0x142: scause
    - supervisor trap cause
    - SRW
- 0x143: stval
    - supervisor bad address or instruction
    - SRW
- 0x144: sip
    - supervisor interrupt pending
    - SRW

#### VM
- 0x180: satp
    - supervisor address translation and protection
    - SRW

#### Debug/Trace
- skip

#### State Enable
- skip

### Machine CSR's

#### Machine Info
- 0xF11: mvendorid
    - vendor ID
    - MRO
    - {32'h0}
        - non-commercial implementation
- 0xF12: marchid
    - architecture ID
    - MRO
    - {32'h0}
        - need to ask RISC-V International if want ID
- 0xF13: mimpid
    - implementation ID
    - MRO
    - {32'h0}
        - don't care for me
- 0xF14: mhartid
    - hardware thread ID
    - MRO
    - assign by core:
        - reset core must be 32'h0
        - remaining cores: 32'h1, 32'h2, 32'h3
- 0xF15: mconfigptr
    - pointer to configuration data structure
    - MRO

#### Trap Setup
- 0x300: mstatus
    - machine status
    - MRW
    - {SD, WPRI[7:0], TSR, TW, TVM, MXR, SM, MPRV, XS[1:0], FS[1:0], MPP[1:0], VS[1:0], SPP, MPIE, UBE, SPIE, WPRI, MIE, WPRI, SIE, WPRI}
        - MIE, SIE: 
            - interrupt enables
            - MIE:
                - M-mode interrupt enable
                - enable interrupts when executing in M-mode
                - WARL
            - SIE:
                - S-mode interrupt enable
                - enable interrupts when executing in S-mode
                - WARL
            - regardless of these values, still never get interrupted by interrupts for lower privelege modes
                - M-mode execution cannot be interrupted by S-mode level interrupt
            - regardless of these value, can still get interrupted by interrupts for higher privilege modes
                - S-mode execution can always be interrupted by M-mode level interrupt
                - U-mode execution can always be interrupted by M-mode or S-mode level interrupts
        - MPIE, SPIE, MPP, SPP: 
            - previous enables and privelege modes
            - make up two-level privelege mode stack
                - two-level in that save current and previous mode info
                - SW must be careful to maintain this stack e.g. guarantee no exceptions while saving privelege mode stack
            - MPIE:
                - M-mode previous interrupt enable
                - MIE value before this trap
                    - SW can restore MIE to this MPIE value if wants to disable interrupts to take care of this trap
                - WARL
            - SPIE:
                - S-mode previous interrupt enable
                - SIE value before this trap
                    - SW can restore SIE to this SPIE value if wants to disable interrupts to take care of this trap
                - WARL
            - MPP[1:0]:
                - M-mode previous privelege mode
                - 00: previously U-mode
                - 01: previously S-mode
                - 10: reserved
                - 11: previously M-mode
                - WARL
            - SPP:
                - S-mode previous privelege mode
                - 0: previously U-mode
                - 1: previously S-mode
                - WARL
            - HW support:
                - trap to M-mode
                    - set MPIE with MIE value
                    - set MPP with mode trapped from
                - trap to S-mode
                    - set SPIE with SIE value
                    - set SPP with mode trapped from
                - MRET
                    - set mode with MPP value
                    - set MIE with MPIE value
                    - set MPIE = 1'b1
                    - set MPP = 2'b00 (U-mode)
                    - set MPRV = 1'b0 if MPP != 2'b11 (M-mode)
                - SRET
                    - set mode with SPP value
                    - set SIE with SPIE value
                    - set SPIE = 1'b1
                    - set SPP = 1'b0 (U-mode)
                    - set MPRV = 1'b0
        - MPRV:
            - Modify Privelege
            - MPRV = 0:
                - use executing privelege mode's DATA (load/store/amo) memory translation and protection rules
            - MPRV = 1:
                - use DATA (load/store/amo) memory translation and protection rules designated by the MPP privelege mode
            - WARL
            - essentially, SW can enable translation and protection for M-mode loads and stores
                - e.g. misaligned load, can directly use virtual address that S-mode or U-mode tried to access
            - MPRV = 0 guaranteed for U-mode and S-mode
            - MPRV = 0 OR MPRV = 1 for M-mode
        - MXR: 
            - Make Executable Readable
            - MXR = 0:
                - normal translation and protection rules where can only load from page with R=1
            - MXR = 1:
                - allow loads from pages with X=1 or R=1
            - WARL
            - implies MPRV = 1 for this field to be relevant, when trying to do a translated and protected load in M-mode
        - SUM:
            - Permit Supervisor User Memory Access
            - SUM = 0:
                - S-mode accesses to U=1 pages will fault
            - SUM = 1:
                - S-mode accesses to U=1 pages are permitted
            - WARL
            - implies translation and protection in effect for this field to have an effect
            - relevant to M-mode when MPRV=1 & MPP=S-mode
                - this is when DATA memory accesses are effectively S-mode accesses
        - MBE, SBE, UBE:
            - byte endianness for DATA memory accesses
                - instruction accesses always little-endian
            - 0 for little endian, 1 for big endian
            - UBE = 1'b0:
                - U-mode Byte Endianness
                - WARL
                    - will ignore writes
            - SBE and MBE in mstatush
        - TVM:
            - Trap Virtual Memory
            - TVM = 0:
                - satp CSR reads/writes and SFENCE.VMA allowed in S-mode
            - TVM = 1:
                - satp CSR reads/writes and SFENCE.VMA raise an illegal-instruction exception in S-mode 
            - WARL
        - TW:
            - Timeout Wait
            - TW = 0:
                - S-mode can freely execute WFI
            - TW = 1:
                - S-mode use of WFI either:
                    - waits for bounded time before completing
                    - gives illegal instruction
            - WARL
            - U-mode use of WFI always either:
                - waits for bounded time before completing
                - gives illegal instruction
            - simple: 
                - TW = 1 & S-mode immediately gives illegal instruction
                - U-mode WFI always immediately gives illegal instruction
        - TSR:
            - Trap SRET
            - TSR = 0:
                - SRET is permitted in S-mode
            - TSR = 1:
                - SRET in S-mode raises illegal-instruction exception
            - WARL
        - FS, VS, XS, SD:
            - extension context status
                - 2 bits each for {Off, Initial, Clean, Dirty} states
            - FS[1:0]:
                - FPU state encoding
                - WARL
                    - allow writes and reads for FPU emulation in SW
            - VS[1:0] = 2'b00:
                - Vector state encoding
                - WARL
                    - allow writes and reads for FPU emulation in SW
            - XS[1:0] = 2'b00:
                - additional U-mode extension state encoding
                - WARL
                    - will ignore writes
            - SD:
                - SD = 0:
                    - none of FS, VS, XS dirty
                - SD = 1: 
                    - any of FS, VS, XS dirty
                - read-only
- 0x301: misa
    - ISA and extensions
    - MRW
    - {MXL[1:0], 4'b0000, Extensions[25:0]}
        - MXL[1:0] = 2'b01
            - Machine XLEN
            - WARL
                - will ignore writes
                    - else would need to be able to dynamically change XLEN
            - 2'b01 to denote XLEN = 32
        - Extensions[25:0] = 26'b00000101000001000100000101
            - Extensions A:Z
                - 0: A for Atomic
                - 2: C for Compressed
                - 8: I for RV32I
                - 12: M for Mul/Div
                - 18: S for Supervisor Mode
                - 20: U for User Mode
            - WARL
                - will ignore writes
                    - else would need to be able to dynamically change Extensions
- 0x302: medeleg
    - machine exception delegation
    - MRW
    - all exceptions trap to M-mode by default
    - set bits in medeleg, medelegh for corresponding exceptions to trap to S-mode when executing in S-mode or U-mode
        - corresponding exceptions executing in M-mode still trap to M-mode
    - bit indexes correspond to mcause bit indexes
    - HW support for delegated exception:
        - set scause
        - set sepc
        - set stval
        - set mstatus.SPP following execution mode when trapped
        - set mstatus.SIE = 0
    - HW support for all bits as writeable 0 or 1:
        - means HW support for any exception delegatable 
        - exceptions that aren't possible in lower privileged modes are read-only zero
            - medeleg[11] = 1'b0
- 0x303: mideleg
    - machine interrupt delegation
    - MRW
    - mostly same semantics as medeleg but for interrupts
    - delegated interrupts are ignored in M-mode
        - instead of interrupting to M-mode if executing in M-mode, these are now ignored
    - bit indexes correspond to mcause bit indexes
    - no midelegh
- 0x304: mie
    - machine interrupt enable
    - MRW
    - bit indexes correspond to mcause bit indexes
    - when interrupt into M-mode for interrupt i:
        - either:
            - executing in M-mode and mstatus.MIE = 1'b1
            - executing in S-mode OR U-mode
        - mip[i] = 1'b1 & mie[i] = 1'b1
        - mideleg[i] = 1'b0
    - propagate changes to mip, mie, mstatus, mideleg immediately on MRET, SRET
    - propagate changes to mip, mie, mstatus, mideleg immediately on dependent CSR writes
    - M-mode interrupts take priority over S-mode delegated interrupts
    - bits of supported interrupts can be written by CSR writes
    - bits of unsupported interrupts are read-only zero
    - {upper16[15:0], 2'b00, LCOFIE, 1'b0, MEIE, 1'b0, SEIE, 1'b0, MTIE, 1'b0, STIE, 1'b0, MSIE, 1'b0, SSIE, 1'b0}
        - upper16[15:0] = 16'h0:
            - upper 16 bits are implementation defined
            - HW custom interrupts here
                - none planned right now
        - LCOFIE = 1'b0:
            - not supported
            - would be used for Sscofpmf extension for counter overflow interrupts
        - MEIE:
            - M External Interrupt enable
        - MTIE:
            - M Timer Interrupt Enable
        - MSIE:
            - M Software Interrupt Enable
        - 
- 0x305: mtvec
    - machine trap-vector base-address
    - MRW
    - {BASE[31:2], MODE[1:0]}
        - BASE:
            - base address of trap PC
            - give 4-byte aligned upper 30 PC bits
            - WARL
        - MODE:
            - trap vectorization enable
            - WARL
            - MODE = 2'b00: Direct
                - all exceptions and interrupts:
                    - PC <= BASE
            - MODE = 2'b01: Vectored
                - exceptions:
                    - PC <= BASE
                - interrupts:
                    - PC <= BASE + 4 * (interrupt cause)
            - MODE = 2'b10, 2'b11:
                - reserved
                - WARL so force to 2'b00 or 2'b01 if try to write these
- 0x306: mcounteren
    - machine counter enable
    - MRW
- 0x310: mstatush
    - upper 32 bits of mstatus
    - MRW
    - {WPRI[25:0], MBE, SBE, WPRI[3:0]}
        - MBE, SBE:
            - byte endianness for DATA memory accesses
                - instruction accesses always little-endian
            - 0 for little endian, 1 for big endian
            - MBE = 1'b0:
                - M-mode Byte Endianness
                - WARL
                    - will ignore writes
            - SBE = 1'b0:
                - S-mode Byte Endianness
                - WARL
                    - will ignore writes
- 0x312: medelegh
    - upper 32 bits of medeleg

#### Trap Handling
- 0x340: mscratch
    - scrath register for machine trap handlers
    - MRW
- 0x341: mepc
    - machine exception PC
    - MRW
- 0x342: mcause
    - machine trap cause
    - MRW
- 0x343: mtval
    - machine bad address or instruction
    - MRW
- 0x344: mip
    - machine interrupt pending
    - use this reg to give indication of existent interrupt
        - i.e. use these actual reg bits to determine if interrupt core
    - MRW
    - bit indexes correspond to mcause bit indexes
    - bits of supported interrupts can be cleared to 0 by CSR writes
    - bits of unsupported interrupts are read-only zero
    - {upper16[15:0], 2'b00, LCOFIP, 1'b0, MEIP, 1'b0, SEIP, 1'b0, MTIP, 1'b0, STIP, 1'b0, MSIP, 1'b0, SSIP, 1'b0}
        - upper16[15:0] = 16'h0:
            - upper 16 bits are implementation defined
            - HW custom interrupts here
                - none planned right now
        - LCOFIP = 1'b0:
            - not supported
            - would be used for Sscofpmf extension for counter overflow interrupts
        - MEIP:
            - M External Interrupt Pending
            - read-only by CSR instr's
            - set and cleared by PLIC
        - MTIP:
            - M Timer Interrupt Pending
            - read-only by CSR instr's
            - set and cleared by writing to mem-mapped M-mode timer compare CSR
        - MSIP:
            - M Software Interrupt Pending
            - read-only by CSR instr's
            - set and cleared by mem-mapped IPI CSR's
    - see mie ^ for remaining semantics
    
#### Config
- skip

#### Memory Protection
- skip

#### State Enable
- skip

#### Non-Maskable Interrupt Handling
- skip

#### Counters, Timers
- 0xB00: mcycle
    - machine cycle counter
    - MRW
- 0xB02: minstret
    - machine instructions retired counter
    - MRW
- 0xB80: mcycleh
    - upper 32 bits of mcycle
    - MRW
- 0xB82: minstreth
    - upper 32 bits of minstret
    - MRW
- 0x320: mcountinhibit
    - machine counter inhibit register
    - MRW

#### Debug/Trace
- skip

#### Debug Mode
- skip