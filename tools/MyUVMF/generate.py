from jinja2 import Environment, FileSystemLoader
import myUVMF_lib
import sys

# Spec File Path - can change but must be valid YAML
# spec = 'demo/alu.yaml'

# UVM template files 
templates = [
    'agent.sv.jinja2', 
    'driver.sv.jinja2', 
    'env.sv.jinja2',
    'interface.sv.jinja2', 
    'monitor.sv.jinja2', 
    'sequence_item.sv.jinja2',
    'sequencer.sv.jinja2',
    'scoreboard.sv.jinja2',
    'test.sv.jinja2',
    'testbench.sv.jinja2'
]

def main():
    spec = sys.argv[1]
    print(f"YAML Config File: {spec}")
    # Load YAML spec
    DUT_spec = myUVMF_lib.load_spec(spec)
    # Create Jinja2 Environment
    env = Environment(loader=FileSystemLoader('.'))
    # Generate corresponding UVM files for Jinja2 templates
    for template in templates:
        uvm_file    = myUVMF_lib.get_file_stem(template)
        j2_template = env.get_template(f'jinja/{template}')
        sv_result   = j2_template.render(DUT_spec)

        myUVMF_lib.write_testbench(sv_result, uvm_file)
        myUVMF_lib.write_testbench_from_yaml(sv_result, uvm_file, spec)


if __name__=="__main__":
    main()