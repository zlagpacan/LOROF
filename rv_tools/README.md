# rv_tools
Directory containing custom LOROF RISC-V tools

## Implemented Tools:

### asm.py
- RISC-V Assembler
- translate .asm format to .mem format
- input: .asm format
    - untranslated instructions and data within verilog .mem format which can read in with $readmemh()
    - RISC-V assembly except:
        - no labels
        - no defined segments
        - essentially nothing that linker would use, all code and data information static
    - can manually select byte address to start segments from using @<address>
    - can manually insert data bytes using raw numbers
        - decimal
        - hex using 0x
        - binary using 0b
- output: .mem format
    - verilog .mem format which can read in with $readmemh()

### iss.py
- RISC-V Instruction Set Simulator
- simulate RISC-V hart execution given memory state
- planned functionality
    - give final memory state for starting memory state
    - give instruction-by-instruction expected architectural state for verification

## Planned Tools:
- instruction generator
    - design to assist in creating testcases