# --- Modules --- #
import re
from collections import defaultdict
import datetime
import argparse

# --- Parse QuestaSim Transcript --- #
def parse_log_file(log_file_path):
    result_lines = []
    grouped_results = defaultdict(list)
    failed_timestamps = defaultdict(list)

    with open(log_file_path, 'r') as file:
        for line in file:
            # Check if 'PASSED' or 'FAILED' is in the line (case-insensitive) TODO: may change to caps only
            if 'PASSED' in line.upper() or 'FAILED' in line.upper():
                result_lines.append(line.strip())
                
                # Regex for SVA_INFO and UVM_INFO to trace to scbd or assertion module
                match = re.search(r'@\s*(\d+).*Test Case:\s*([A-Za-z0-9_-]+)\s*[:]\s*(PASSED|FAILED)', line)
                if match:
                    timestamp = match.group(1).strip()
                    tag = match.group(2)
                    result = match.group(3)

                    info_type = ''
                    if 'UVM_INFO' in line:
                        info_type = 'UVM'
                    elif 'SVA_INFO' in line:
                        info_type = 'SVA'

                    grouped_results[tag].append((line.strip(), result, info_type))
                    
                    # Log all instances of a testcase if the parent test case failed
                        # - may change in the future for larger modules or turn on/off via makefile
                    if result == 'FAILED':
                        failed_timestamps[tag].append(timestamp)

    return result_lines, grouped_results, failed_timestamps

def evaluate_group(group_lines):
    # Test cases that have any failed instances are blanked classified as failed
    for line, result, _ in group_lines:
        if 'FAILED' in result.upper():
            return 'FAIL'
    return 'PASS'

def print_group_ratings(grouped_by_tag, failed_timestamps, output_file):
    timestamp_width = 6
    status_width = 7

    console_separator_length = 55  
    file_separator_length = 65

    timestamp_str = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    header = f"Script run on: {timestamp_str}\n"
    print(header)
    output_file.write(header)

    console_separator = '-' * console_separator_length
    file_separator = '-' * file_separator_length

    first_group = True
    print(console_separator)
    output_file.write(file_separator + '\n')

    for tag, lines in grouped_by_tag.items():
        if not first_group:
            print(console_separator)  # Print separator to console
            output_file.write(file_separator + '\n')  # Write separator to log file

        first_group = False  # After the first group, set the flag to False

        rating = evaluate_group(lines)
        
        # Determine test case type (UVM or SVA)
        info_type = lines[0][2] if lines else ''
        
        # Print the group header with color codes (PASS/FAIL)
        if rating == 'FAIL':
            console_output = f"\033[41m-\033[0m {tag.ljust(console_separator_length - 20)} ({info_type}) : \033[41m{rating.ljust(5)}\033[0m \033[41m-\033[0m"
            print(console_output)
            output_file.write(f"[FAIL] {tag.ljust(file_separator_length - 30)} ({info_type}) : {rating.ljust(5)} [FAIL]\n")

            print("    Instances:")
            output_file.write("    Instances:\n")
            for line, result, _ in lines:
                timestamp = re.search(r'@\s*(\d+)', line).group(1)
                status = result.upper()

                instance_output = f"        - Timestamp: {timestamp.ljust(timestamp_width)} : {status.ljust(status_width)} -"
                print(instance_output)
                output_file.write(f"        - Timestamp: {timestamp.ljust(timestamp_width)} : {status.ljust(status_width)} -\n")
        else:
            console_output = f"\033[42m-\033[0m {tag.ljust(console_separator_length - 20)} ({info_type}) : \033[42m{rating.ljust(5)}\033[0m \033[42m-\033[0m"
            print(console_output)
            output_file.write(f"[PASS] {tag.ljust(file_separator_length - 30)} ({info_type}) : {rating.ljust(5)} [PASS]\n")

    print(console_separator)
    output_file.write(file_separator + '\n')

def main():
    # Arg parse for Makefile capabilities 
        # - TODO: may need to add arg if want to toggle instance reporting 
    parser = argparse.ArgumentParser(description="Process UVM log file and generate pass/fail ratings.")
    parser.add_argument("input_file", help="Path to the input log file")
    parser.add_argument("output_file", help="Path to the output file where results will be written")

    args = parser.parse_args()
    
    input_file = args.input_file
    output_file_path = args.output_file

    all_lines, grouped_by_tag, failed_timestamps = parse_log_file(input_file)

    with open(output_file_path, 'w') as output_file:
        print("Group Pass/Fail Ratings:")
        print_group_ratings(grouped_by_tag, failed_timestamps, output_file)

if __name__ == "__main__":
    main()
