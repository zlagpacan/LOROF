# CSR List
ISA: RV32IMAC_Zicsr_Zifencei Sv32

- CSR's have associated privilege level where this privelege level and higher privilege levels can access it

General Rules
- csr[11:0]
    - csr[11:10]
        - 00, 01, 10:
            - read/write
        - 11:
            - read-only
    - csr[9:8]
        - lowest privilege level that can access
        - 00:
            - user-level
        - 01:
            - supervisor-level
        - 10:
            - hypervisor-level
        - 11:
            - machine-level

- raise illegal instruction exception if current privilege level not allowed to access
- raise illegal instruciton exception if try to write to read-only register
    - writes to read-only fields of read/write registers are simply ignored
