import re
from collections import defaultdict
import datetime
import argparse

def parse_log_file(log_file_path):
    result_lines = []
    grouped_results = defaultdict(list)
    failed_timestamps = defaultdict(list)

    # Open the log file
    with open(log_file_path, 'r') as file:
        for line in file:
            # Check if 'PASSED' or 'FAILED' is in the line (case-insensitive)
            if 'PASSED' in line.upper() or 'FAILED' in line.upper():
                result_lines.append(line.strip())  # Add the line to the list, stripping any extra whitespace
                
                # Updated regex to handle both formats: SVA_INFO and UVM_INFO
                match = re.search(r'@\s*(\d+).*Test Case:\s*([A-Za-z0-9_-]+)\s*[:]\s*(PASSED|FAILED)', line)
                if match:
                    timestamp = match.group(1).strip()  # Extract the timestamp
                    tag = match.group(2)  # Extract the test case tag
                    result = match.group(3)  # Extract PASSED/FAILED result

                    # Check for 'UVM_INFO' or 'SVA_INFO' in the line
                    info_type = ''
                    if 'UVM_INFO' in line:
                        info_type = 'UVM'
                    elif 'SVA_INFO' in line:
                        info_type = 'SVA'

                    # Add the line under the respective tag with the info type
                    grouped_results[tag].append((line.strip(), result, info_type))  # Store info_type with the result
                    
                    # If the result is 'FAILED', store the timestamp
                    if result == 'FAILED':
                        failed_timestamps[tag].append(timestamp)

    return result_lines, grouped_results, failed_timestamps

def evaluate_group(group_lines):
    # Check if there is any 'FAILED' result in the group
    for line, result, _ in group_lines:
        if 'FAILED' in result.upper():
            return 'FAIL'  # If any "FAILED" exists, the group gets a FAIL rating
    return 'PASS'  # If no "FAILED", the group gets a PASS rating

def print_group_ratings(grouped_by_tag, failed_timestamps, output_file):
    timestamp_width = 6  # Width for the timestamp field for consistent padding
    status_width = 7  # Width for the status field (PASSED/FAILED)

    # Console separator length (for better readability on the console)
    console_separator_length = 55  
    # Log file separator length (slightly longer for alignment in file)
    file_separator_length = 65

    # Add the timestamp to the log output and console
    timestamp_str = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    header = f"Script run on: {timestamp_str}\n"
    print(header)  # Print to console
    output_file.write(header)  # Write to log file

    # Define different separators for console and file output
    console_separator = '-' * console_separator_length  # Shorter separator for console
    file_separator = '-' * file_separator_length  # Longer separator for file

    # Iterate over the grouped results and assign PASS or FAIL rating to each group
    first_group = True  # Flag to manage the separator printing
    print(console_separator)  # Print separator to console
    output_file.write(file_separator + '\n')  # Write separator to log file

    for tag, lines in grouped_by_tag.items():
        # Print separator line before each group (only for subsequent groups)
        if not first_group:
            print(console_separator)  # Print separator to console
            output_file.write(file_separator + '\n')  # Write separator to log file

        first_group = False  # After the first group, set the flag to False

        rating = evaluate_group(lines)
        
        # Determine the info type (UVM or SVA)
        info_type = lines[0][2] if lines else ''  # Get the info type from the first line in the group
        
        # Print the group header with color codes (PASS/FAIL)
        if rating == 'FAIL':
            console_output = f"\033[41m-\033[0m {tag.ljust(console_separator_length - 20)} ({info_type}) : \033[41m{rating.ljust(5)}\033[0m \033[41m-\033[0m"
            print(console_output)
            output_file.write(f"[FAIL] {tag.ljust(file_separator_length - 30)} ({info_type}) : {rating.ljust(5)} [FAIL]\n")

            # Indent and print the timestamps for failed and passed test cases
            print("    Instances:")
            output_file.write("    Instances:\n")
            for line, result, _ in lines:
                timestamp = re.search(r'@\s*(\d+)', line).group(1)  # Extract timestamp
                status = result.upper()

                # Print instances with '-' and '*' (no color highlighting)
                instance_output = f"        - Timestamp: {timestamp.ljust(timestamp_width)} : {status.ljust(status_width)} *"
                print(instance_output)
                output_file.write(f"        - Timestamp: {timestamp.ljust(timestamp_width)} : {status.ljust(status_width)} *\n")
        else:
            console_output = f"\033[42m-\033[0m {tag.ljust(console_separator_length - 20)} ({info_type}) : \033[42m{rating.ljust(5)}\033[0m \033[42m-\033[0m"
            print(console_output)
            output_file.write(f"[PASS] {tag.ljust(file_separator_length - 30)} ({info_type}) : {rating.ljust(5)} [PASS]\n")

    # Print final separator after the last group
    print(console_separator)  # Print final separator to console
    output_file.write(file_separator + '\n')  # Write final separator to log file

def main():
    # Set up argument parser
    parser = argparse.ArgumentParser(description="Process UVM log file and generate pass/fail ratings.")
    parser.add_argument("input_file", help="Path to the input log file")
    parser.add_argument("output_file", help="Path to the output file where results will be written")
    
    # Parse arguments
    args = parser.parse_args()
    
    input_file = args.input_file
    output_file_path = args.output_file

    # Parse the log file
    all_lines, grouped_by_tag, failed_timestamps = parse_log_file(input_file)

    # Open the output file for writing
    with open(output_file_path, 'w') as output_file:
        print("Group Pass/Fail Ratings:")
        print_group_ratings(grouped_by_tag, failed_timestamps, output_file)

if __name__ == "__main__":
    main()
