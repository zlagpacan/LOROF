from jinja2 import Environment, FileSystemLoader
import myUVMF_lib
import sys

# UVM Components - Generic Architecture (minus sequences)
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
    # Directory overwrite warning
    if myUVMF_lib.warn_and_confirm_override():
        spec = sys.argv[1]
        print(f"#  Analyzing yaml specification file : {spec}...")
        # Load YAML spec
        DUT_spec = myUVMF_lib.load_spec(spec)
        # Create Jinja2 Environment
        print("#  nitializing jinja2 template...\n#")
        env = Environment(loader=FileSystemLoader('.'))
        # Generate corresponding UVM files for Jinja2 templates
        for template in templates:
            
            print(f"#  - Generating UVM component from {template} template...")
            uvm_file    = myUVMF_lib.get_file_stem(template)
            j2_template = env.get_template(f'jinja/{template}')
            sv_result   = j2_template.render(DUT_spec)
            
            print(f"#  - Copying    UVM component from {template} template into yaml 'Output_Path'\n#")
            myUVMF_lib.write_testbench(sv_result, uvm_file)
            myUVMF_lib.write_testbench_from_yaml(sv_result, uvm_file, spec)
    else:
        # Exit or handle the stop condition
        print("#  Denied tool permissions to overwrite Output_Path in yaml. Exiting script...")
    
if __name__=="__main__":
    main()