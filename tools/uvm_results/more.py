import re
from collections import defaultdict
import datetime

def parse_log_file(log_file_path):
    result_lines = []
    grouped_results = defaultdict(list)
    failed_timestamps = defaultdict(list)
    tag_info = defaultdict(str)  # To store info (SVA/UVM) for each tag

    # Open the log file
    with open(log_file_path, 'r') as file:
        for line in file:
            # Check if 'PASSED' or 'FAILED' is in the line (case-insensitive)
            if 'PASSED' in line.upper() or 'FAILED' in line.upper():
                result_lines.append(line.strip())  # Add the line to the list, stripping any extra whitespace
                
                # Updated regex to handle both formats: SVA_INFO and UVM_INFO
                match = re.search(r'@\s*(\d+).*Test Case:\s*([A-Za-z0-9_-]+)\s*[:]\s*(PASSED|FAILED).*?(SVA_INFO|UVM_INFO)', line)
                if match:
                    timestamp = match.group(1).strip()  # Extract the timestamp
                    tag = match.group(2)  # Extract the test case tag
                    result = match.group(3)  # Extract PASSED/FAILED result
                    info_type = match.group(4)  # Extract SVA_INFO or UVM_INFO

                    # Store info type (either 'SVA' or 'UVM') for each tag
                    tag_info[tag] = info_type.replace('_INFO', '')  # Remove '_INFO' to just get 'SVA' or 'UVM'

                    grouped_results[tag].append((line.strip(), result))  # Add the line under the respective tag
                    
                    # If the result is 'FAILED', store the timestamp
                    if result == 'FAILED':
                        failed_timestamps[tag].append(timestamp)

    return result_lines, grouped_results, failed_timestamps, tag_info

def evaluate_group(group_lines):
    # Check if there is any 'FAILED' result in the group
    for line, result in group_lines:
        if 'FAILED' in result.upper():
            return 'FAIL'  # If any "FAILED" exists, the group gets a FAIL rating
    return 'PASS'  # If no "FAILED", the group gets a PASS rating

def print_group_ratings(grouped_by_tag, failed_timestamps, tag_info, output_file):
    timestamp_width = 6  # Width for the timestamp field for consistent padding
    status_width = 7  # Width for the status field (PASSED/FAILED)

    # Console separator length (for better readability on the console)
    console_separator_length = 50  
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

    for tag, lines in grouped_by_tag.items():
        # Print separator line before each group (only for subsequent groups)
        if not first_group:
            print(console_separator)  # Print separator to console
            output_file.write(file_separator + '\n')  # Write separator to log file

        first_group = False  # After the first group, set the flag to False

        rating = evaluate_group(lines)
        
        # Get the SVA or UVM info for the tag
        info_type = tag_info.get(tag, 'UNKNOWN')

        # Print the group header with color codes (PASS/FAIL)
        if rating == 'FAIL':
            console_output = f"\033[41m-\033[0m {tag.ljust(console_separator_length - 10)} ({info_type}): {rating.ljust(5)} \033[41m-\033[0m"
            print(console_output)
            output_file.write(f"[FAIL] {tag.ljust(file_separator_length - 10)} ({info_type}): {rating.ljust(5)} [FAIL]\n")

            # Indent and print the timestamps for failed and passed test cases in console
            print("    Instances:")
            output_file.write("    Instances:\n")
            for line, result in lines:
                timestamp = re.search(r'@\s*(\d+)', line).group(1)  # Extract timestamp
                status = result.upper()

                # Console output with color highlight (PASS/FAIL)
                if status == 'FAILED':
                    instance_output = f"        \033[41m-\033[0m Timestamp: {timestamp.ljust(timestamp_width)} : {status.ljust(status_width)} \033[41m-\033[0m"
                    print(instance_output)
                    output_file.write(f"        [FAILED] Timestamp: {timestamp.ljust(timestamp_width)} : {status.ljust(status_width)} [FAILED]\n")
                else:
                    instance_output = f"        \033[42m-\033[0m Timestamp: {timestamp.ljust(timestamp_width)} : {status.ljust(status_width)} \033[42m-\033[0m"
                    print(instance_output)
                    output_file.write(f"        [PASSED] Timestamp: {timestamp.ljust(timestamp_width)} : {status.ljust(status_width)} [PASSED]\n")
        else:
            console_output = f"\033[42m-\033[0m {tag.ljust(console_separator_length - 10)} ({info_type}): {rating.ljust(5)} \033[42m-\033[0m"
            print(console_output)
            output_file.write(f"[PASS] {tag.ljust(file_separator_length - 10)} ({info_type}): {rating.ljust(5)} [PASS]\n")

    # Print final separator after the last group
    print(console_separator)  # Print final separator to console
    output_file.write(file_separator + '\n')  # Write final separator to log file

def main():
    # Example usage:
    log_file_path = 'uvm_results.log'  # Set log file path here

    all_lines, grouped_by_tag, failed_timestamps, tag_info = parse_log_file('../../uvm/alu/transcript')

    # Open the log file for writing
    with open(log_file_path, 'w') as output_file:
        print("Group Pass/Fail Ratings:")
        print_group_ratings(grouped_by_tag, failed_timestamps, tag_info, output_file)
    
if __name__=="__main__":
    main()
