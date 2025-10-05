#!/usr/bin/python3

import sys
import argparse

if __name__ == "__main__":
    print(" ".join(sys.argv))

    parser = argparse.ArgumentParser()
    parser.add_argument("input_mem_file_path")
    parser.add_argument("output_mem_file_path")
    args = parser.parse_args()
    print(args)

    pc = 0x0
    reg_file = [0x0 for x in range(32)]