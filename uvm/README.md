# UVM Directory #

---
### Description ###
<br>

Documentation : [LOROF/Verification](https://purdue0-my.sharepoint.com/personal/zlagpaca_purdue_edu/_layouts/15/Doc.aspx?sourcedoc={bf423cb8-97ef-4f09-9179-f3cb80df435d}&action=edit&wd=target%28Verification.one%7Cd7dea935-a95a-4540-8807-f3be7e06814c%2F%29&wdorigin=717)

<br>

The UVM directory is where the official verification team testbenches reside. Each module's directory contains the following...

    > testbench
        - contains the UVM testbench for the module
        - this will look different module to module depending on number of agents and external classes used

    > MyUVMF_output
        - generated testbench from MyUVMF
        - stored in a seperate directory to prevent malicous writes to the testbench directory

    - results.rpt
        - test case results generated from QuestaSim transcript

    - <module>_uvm.drawio.pdf
        - UVM architecture diagram for the proposed testbench

    - <module>.yaml
        - YAML spec used for MyUVMF
