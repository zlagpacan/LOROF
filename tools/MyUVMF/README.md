# My-UVMF

## Description

This is a rendition of MyUVMF that I am developing as a sort of intermediary between industry level (UVMF) and bare bones UVM testbench development from scratch. It takes DUT-centric YAML and then generates the UVM scaffolding.

This acheives two things...

    1. Consistent naming convention and reduced build/run errors

    2. Automated tesbench development to speed up verification process

This tool will be relaesed in versions and hte first few versions will be very ad-hoc. The idea is that this sits in your project repo and then you customize its flow based on your needs.

* See how it is implemented in my project - LOROF - on my GitHub profile

---

## Version

Version : 1.0

This version of MyUVMF generates a generic UVM architecture and connects the components. What the user still needs to do in this verion...

    - Add constraints to the stimulus
    - Add custom typedefs if used
    - Create test seqeunces
    - Create scoreboards (beyond scaffolding)
    - Create test procedure
    - Instantiate DUT in testbench and other testbench features

This seems like a lot, but all of this is more of the brain work that verification engineers should be doing instead of spending extra time creating all of the redundant UVM scaffolding. 

---

### How it works
User adds DUT and testbench specs to YAML file. Then generate.py makes the UVM testbench files.


## Release Outline

- 1.00 
    - Generic UVM testbench scaffolding
    - Creates single agent + interface


#### Next Releases

- 2.0 
    - Multi-agent support
    - Typedefs
    - Increased YAML features
---
