"""
    Filename: wrapper_generator.py
    Author: zlagpacan
    Description: Script to automatically generate simple wrappers for a target module.
    Notes:
        - need to manually set struct fields
            - if use struct, also need to manually enumerate connections in wrapper for synthesized
        - need to manually create signals to allow type conversion b/w enums and pure logic arrays
            - output: constantly assign pure logic array synthesized module output to enum wrapper value
                - explicit enum typecast
            - input: constantly assign enum wrapper value to pure logic array synthesized module input
                - explicit pure logic array typecast
                    - may not be necessary?
"""

import argparse
import os
import re

PRINTS = False
BLOCK_IS_SEQ = False

class Signal():
    def __init__(self, io, type, name):
        self.io = io
        self.type = type
        self.name = name

class Param():
    def __init__(self, name, type, default_value):
        self.name = name
        self.type = type
        self.default_value = default_value

def parse_design(design_lines):

    # iterate through design lines looking for design name
    design_name = None
    for line in design_lines:
        if line.lstrip().startswith("module"):
            design_name = line[len("module"):].lstrip().rstrip().rstrip("(#").rstrip()
            break

    assert design_name, "could not find design name"
    print(f"design_name = {design_name}") if PRINTS else None

    # iterate through design lines looking for design components
    design_signals = []
    design_params = []
    design_includes_and_imports = []
    inside_multiline_comment = False
    inside_io = False
    inside_param = False
    for line_index, line in enumerate(design_lines):

        # include or import
        if line.lstrip().startswith("`include"):
            design_includes_and_imports.append(line)
            continue
        if line.lstrip().startswith("import"):
            design_includes_and_imports.append(line)
            continue

        # try to exit io
        if line.lstrip().rstrip() == ");":
            assert inside_io, "found I/O exit \");\" when not inside I/O def"
            inside_io = False
            break

        # when inside I/O signal def
        if inside_io:
            stripped_line = line.lstrip().rstrip().rstrip(",")

            # skip seq comment
            if stripped_line.startswith("//") and "seq" in stripped_line:
                continue

            # skip CLK and nRST
            if "CLK" in stripped_line or "nRST" in stripped_line:
                global BLOCK_IS_SEQ
                BLOCK_IS_SEQ = True
                continue

            # add any empty lines as signals
            if not stripped_line:
                design_signals.append(Signal("", "empty", line))
                continue

            # add any top level comments as signals
            if stripped_line.startswith("//"):
                design_signals.append(Signal("", "comment", line))
                continue

            # cut off any mid-line comments
            if "//" in stripped_line:
                stripped_line = stripped_line[:stripped_line.index("//")].rstrip().rstrip(",")

            # split line at spaces
                # first split is input vs. output
                # last split is signal name
                # middle splits are type 
            tuple_line = tuple(stripped_line.split())
            print(tuple_line) if PRINTS else None
            design_signals.append(Signal(tuple_line[0], " ".join(tuple_line[1:-1]), tuple_line[-1]))
            continue

        # ignore empty lines
        if not line.lstrip().rstrip():
            print(f"found empty line at line {line_index}") if PRINTS else None
            continue

        # ignore comment lines
        if "/*" in line:
            print(f"entering multiline comment at line {line_index}") if PRINTS else None
            inside_multiline_comment = True
            continue
        if inside_multiline_comment:
            if "*/" in line:
                print(f"exiting multiline comment at line {line_index}") if PRINTS else None
                inside_multiline_comment = False
            continue
        if line.lstrip().rstrip().startswith("//"):
            print(f"found comment at line {line_index}") if PRINTS else None
            continue

        # try to enter io
        if (line.lstrip().startswith(")") and line.rstrip().endswith("(")) or (
            line.lstrip().startswith("module") and line.rstrip().endswith("(") and "#" not in line):
            inside_io = True
            inside_param = False
            continue

        # when still inside parameter section
        if inside_param:
            # expect non-empty lines to all be parameters
            if (line.lstrip().startswith("parameter")):
                # grab last string before " = " as param name
                type_name_string = line[line.index("parameter ")+len("parameter "):line.index(" = ")].rstrip()
                res = re.search(r'(\S+)$', type_name_string)
                param_name = res.group(1)
                param_type = type_name_string[:type_name_string.index(param_name)].rstrip()
                design_params.append(Param(param_name, param_type, line[line.index(" = ")+len(" = "):].rstrip().rstrip(",")))
            else:
                print("WARNING: found unexpected parameter section line:", line)

        # try to enter param
        if (line.lstrip().startswith("module") and line.rstrip().endswith("(") and "#" in line):
            inside_param = True
            continue

    if inside_io:
        print("WARNING: did not find clean I/O section exit")

    assert design_signals, "could not find any signals in design"

    return design_name, design_signals, design_params, design_includes_and_imports

def generate_wrapper(wrapper_base_lines, design_name, design_signals, design_params, design_includes_and_imports):
    
    output_lines = []

    # iterate through wrapper base lines adding in info based on design_name and design_signals as go
    num_found = 0
    for line_index, line in enumerate(wrapper_base_lines):

        # check for <design_name> line
        if "<design_name>" in line:
            replaced_line = line.replace("<design_name>", design_name)
            print(f"found <design_name> in line") if PRINTS else None
            print(f"old line: {line}") if PRINTS else None
            print(f"replaced line: {replaced_line}") if PRINTS else None

            output_lines.append(replaced_line)

            num_found += 1
            continue

        # check for <includes and imports> line
        if "<includes and imports>" in line:
            print(f"found <includes and imports> at line {line_index}") if PRINTS else None

            # insert includes and imports lines
            output_lines.extend(design_includes_and_imports)

            num_found += 1
            continue

        # check for <DUT params>
        if line.lstrip().rstrip() == "<DUT params>":
            print(f"found <DUT params> at line {line_index}") if PRINTS else None

            # iterate through params adding param lines
            for i, param in enumerate(design_params):
                if i < len(design_params) - 1:
                    output_lines.extend([
                        f"\tparameter {param.type}{' ' if param.type else ''}{param.name} = {param.default_value},\n",
                    ])
                else:
                    output_lines.extend([
                        f"\tparameter {param.type}{' ' if param.type else ''}{param.name} = {param.default_value}\n",
                    ])

            num_found += 1
            continue

        # check for <wrapper io signals>
        if line.lstrip().rstrip() == "<wrapper io signals>":
            print(f"found <wrapper io signals> at line {line_index}") if PRINTS else None

            # iterate through design_signals adding wrapper io signals declaration
            wrapper_io_signal_lines = []
            for signal in design_signals:
                
                # input
                if signal.io == "input":
                    wrapper_io_signal_lines.extend([
                        f"\tinput {signal.type} next_{signal.name},\n",
                    ])

                # output
                elif signal.io == "output":
                    wrapper_io_signal_lines.extend([
                        f"\toutput {signal.type} last_{signal.name},\n",
                    ])

                # empty
                elif signal.type == "empty":
                    wrapper_io_signal_lines.extend([
                        f"\n"
                    ])
                    
                # comment
                elif signal.type == "comment":
                    wrapper_io_signal_lines.extend([
                        f"{signal.name}"
                    ])

                # not input or output
                else:
                    assert False, f"invalid input vs. output for signal {signal}"

            # remove comma from last non-comment
            found_last_comma = False
            for i in range(-1, -1 - len(wrapper_io_signal_lines), -1):
                if wrapper_io_signal_lines[i].endswith(",\n"):
                    wrapper_io_signal_lines[i] = wrapper_io_signal_lines[i].rstrip().rstrip(",") + "\n"

                    found_last_comma = True
                    break

            output_lines.extend(wrapper_io_signal_lines)

            assert found_last_comma, "in wrapper io signals, did not find signal assignment ending in comma"

            num_found += 1
            continue

        # check for <raw signals>
        if line.lstrip().rstrip() == "<raw signals>":
            print(f"found <raw signals> at line {line_index}") if PRINTS else None

            # iterate through design_signals adding to raw module signals
            raw_signal_lines = []
            for signal in design_signals:
                
                # input or output
                if signal.io == "input" or signal.io == "output":
                    raw_signal_lines.extend([
                        f"\t{signal.type} {signal.name};\n",
                    ])

                # empty
                elif signal.type == "empty":
                    raw_signal_lines.extend([
                        f"\n"
                    ])
                    
                # comment
                elif signal.type == "comment":
                    raw_signal_lines.extend([
                        f"{signal.name}"
                    ])

                # not input or output
                else:
                    assert False, f"invalid input vs. output for signal {signal}"

            output_lines.extend(raw_signal_lines)

            num_found += 1
            continue

        # check for <WRAPPED_MODULE instantiation>
        if line.lstrip().rstrip() == "<WRAPPED_MODULE instantiation>":
            print(f"found <WRAPPED_MODULE instantiation> at line {line_index}") if PRINTS else None

            # add beginning of module instantation
            output_lines.extend([
                f"\t{design_name} #(\n",
            ])

            # iterate through params adding param lines
            for i, param in enumerate(design_params):
                # no comma on last
                if i+1 == len(design_params):
                    output_lines.extend([
                        f"\t\t.{param.name}({param.name})\n",
                    ])
                else:
                    output_lines.extend([
                        f"\t\t.{param.name}({param.name}),\n",
                    ])
  
            # add end of module instantiation
            output_lines.extend([
                f"\t) WRAPPED_MODULE (.*);\n",
            ])

            num_found += 1
            continue

        # check for <reset wrapper signals>
        if line.lstrip().rstrip() == "<reset wrapper signals>":
            print(f"found <reset wrapper signals> at line {line_index}") if PRINTS else None

            # iterate through design_signals adding to reset wrapper signals
            reset_wrapper_signal_lines = []
            for signal in design_signals:
                
                # input
                if signal.io == "input":
                    reset_wrapper_signal_lines.extend([
                        f"\t\t\t{signal.name} <= '0;\n",
                    ])

                # output
                elif signal.io == "output":
                    reset_wrapper_signal_lines.extend([
                        f"\t\t\tlast_{signal.name} <= '0;\n",
                    ])

                # empty
                elif signal.type == "empty":
                    reset_wrapper_signal_lines.extend([
                        f"\n"
                    ])
                    
                # comment
                elif signal.type == "comment":
                    reset_wrapper_signal_lines.extend([
                        f"\t\t{signal.name}"
                    ])

                # not input or output
                else:
                    assert False, f"invalid input vs. output for signal {signal}"

            output_lines.extend(reset_wrapper_signal_lines)

            num_found += 1
            continue

        # check for <latched wrapper signals>
        if line.lstrip().rstrip() == "<latched wrapper signals>":
            print(f"found <latched wrapper signals> at line {line_index}") if PRINTS else None

            # iterate through design_signals adding to latched wrapper signals
            latched_wrapper_signal_lines = []
            for signal in design_signals:
                
                # input
                if signal.io == "input":
                    latched_wrapper_signal_lines.extend([
                        f"\t\t\t{signal.name} <= next_{signal.name};\n",
                    ])

                # output
                elif signal.io == "output":
                    latched_wrapper_signal_lines.extend([
                        f"\t\t\tlast_{signal.name} <= {signal.name};\n",
                    ])

                # empty
                elif signal.type == "empty":
                    latched_wrapper_signal_lines.extend([
                        f"\n"
                    ])
                    
                # comment
                elif signal.type == "comment":
                    latched_wrapper_signal_lines.extend([
                        f"\t\t{signal.name}"
                    ])

                # not input or output
                else:
                    assert False, f"invalid input vs. output for signal {signal}"

            output_lines.extend(latched_wrapper_signal_lines)

            num_found += 1
            continue

        # otherwise, regular wrapper base line, add as-is
        output_lines.append(line)

    assert num_found == 11, f"did not find all entries to replace in wrapper_base.txt. num_found = {num_found}\n" + \
        "(may have added more and not updated required num_found in this script)"

    return output_lines

if __name__ == "__main__":

    parser = argparse.ArgumentParser()
    parser.add_argument("design_file_path")
    parser.add_argument("-o", "--output-to-wrapper-file", action="store_true")
    parser.add_argument("-p", "--prints", action="store_true")
    args = parser.parse_args()

    if args.prints:
        PRINTS = True

    # get this script dir so can get wrapper_base.txt and output to /wrappers
    this_script_dir = os.path.dirname(os.path.abspath(__file__))

    # get input design file
        # don't modify given path
    try:
        with open(args.design_file_path, "r") as fp:
            design_lines = fp.readlines()
    except:
        assert False, f"could not find {args.design_file_path}"

    # get wrapper base
        # modify to relative to this script
    wrapper_base_path = os.path.join(this_script_dir, "wrapper_base.txt")
    try:
        with open(wrapper_base_path, "r") as fp:
            wrapper_base_lines = fp.readlines()
    except:
        assert False, "could not find wrapper_base.txt"
            
    # parse design
    design_name, design_signals, design_params, design_includes_and_imports = parse_design(design_lines)

    # generate wrapper
    output_lines = generate_wrapper(wrapper_base_lines, design_name, design_signals, design_params, design_includes_and_imports)

    # write output file
        # modify to relative to this script
    if args.output_to_wrapper_file:
        output_file_name = f"{design_name}_wrapper.sv"
    else:
        output_file_name = "wrapper_output.txt"
    output_file_path = os.path.join(this_script_dir, output_file_name)
    with open(output_file_path, "w") as fp:
        fp.writelines(output_lines)

    print(f"SUCCESS: generated wrapper in {output_file_path}")