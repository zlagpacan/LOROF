import sys
import argparse
import random
import math

from iss import bits, bit, signed32, make_signed

random.seed(0)
PRINTS = False
ITERS = 0

def div_nonrestoring(a, b, signed):
    global ITERS

    if b == 0:
        return 0xFFFFFFFF, a
    if signed:
        if a == 0x80000000 and b == 0xFFFFFFFF:
            return 0x80000000, 0
        a_neg = (a >> 31) & 0b1
        b_neg = (b >> 31) & 0b1
        a_abs = abs(make_signed(a))
        b_abs = abs(make_signed(b))
    else:
        a_neg = 0
        b_neg = 0
        a_abs = a
        b_abs = b

    print(f"a_abs = 0b_{a_abs:032b}") if PRINTS else None
    print(f"b_abs = 0b_{b_abs:032b}") if PRINTS else None

    AQ = a_abs
    print(f"         init AQ = 0b_{bit(AQ, 64)}_{bits(AQ, 63, 32):032b}_{bits(AQ, 31, 0):032b}") if PRINTS else None

    for iter in range(32):
        if bit(AQ, 64):
            AQ = bits(AQ << 1, 64, 0)
            A = bits(AQ, 64, 32)
            A = bits(A + b_abs, 32, 0)
        else:
            AQ = bits(AQ << 1, 64, 0)
            A = bits(AQ, 64, 32)
            A = bits(A - b_abs, 32, 0)
        AQ = (A << 32) + (bits(AQ, 31, 1) << 1) + (not bit(A, 32))
        print(f"after iter {iter:2d} AQ = 0b_{bit(AQ, 64)}_{bits(AQ, 63, 32):032b}_{bits(AQ, 31, 0):032b}") if PRINTS else None

        ITERS += 1

    A = bits(AQ, 64, 32)
    if bit(A, 32):
        A = bits(A + b_abs, 32, 0)

    print(f"        final AQ = 0b_{bit(A, 32)}_{bits(A, 31, 0):032b}_{bits(AQ, 31, 0):032b}") if PRINTS else None

    quotient = bits(AQ, 31, 0)
    remainder = bits(A, 31, 0)

    if a_neg ^ b_neg:
        quotient = bits(-quotient, 31, 0)
    
    if a_neg:
        remainder = bits(-remainder, 31, 0)

    return quotient, remainder

def pe_msb(value):
    return int(math.log2(value))

def div_nonrestoring_skip(a, b, signed):
    global ITERS

    if b == 0:
        return 0xFFFFFFFF, a
    if signed:
        a_neg = (a >> 31) & 0b1
        b_neg = (b >> 31) & 0b1
        a_abs = abs(make_signed(a))
        b_abs = abs(make_signed(b))
    else:
        a_neg = 0
        b_neg = 0
        a_abs = a
        b_abs = b

    print(f"a_abs = 0b_{a_abs:032b}") if PRINTS else None
    print(f"b_abs = 0b_{b_abs:032b}") if PRINTS else None

    # want to do this so skip works better (otherwise would be sizing AQ reg based on b pointlessly)
    if a_abs < b_abs:
        return 0, a
    
    msb_index = pe_msb(a_abs)

    A = 0
    Q = a_abs
    print(f"         init AQ = 0b_{bit(A, 32)}_{bits(A, 31, 0):032b}_{bits(Q, 31, 0):032b}") if PRINTS else None

    for iter in range(msb_index + 1):
        if bit(A, msb_index + 1):
            A = bits(A << 1, 32, 0) + bit(Q, msb_index)
            Q = bits(Q << 1, msb_index, 0)
            A = bits(A + b_abs, 32, 0)
        else:
            A = bits(A << 1, 32, 0) + bit(Q, msb_index)
            Q = bits(Q << 1, msb_index, 0)
            A = bits(A - b_abs, 32, 0)
        Q += (not bit(A, msb_index + 1))
        print(f"after iter {iter:2d} AQ = 0b_{bit(A, 32)}_{bits(A, 31, 0):032b}_{bits(Q, 31, 0):032b}") if PRINTS else None

        ITERS += 1

    if bit(A, 32):
        A = bits(A + b_abs, 32, 0)

    print(f"        final AQ = 0b_{bit(A, 32)}_{bits(A, 31, 0):032b}_{bits(Q, 31, 0):032b}") if PRINTS else None

    quotient = bits(Q, 31, 0)
    remainder = bits(A, 31, 0)

    if a_neg ^ b_neg:
        quotient = bits(-quotient, 31, 0)
    
    if a_neg:
        remainder = bits(-remainder, 31, 0)

    return quotient, remainder

def div_golden(a, b, signed):
    if b == 0:
        return 0xFFFFFFFF, a
    if signed:
        signed_quotient = int(make_signed(a) / make_signed(b))
        quotient = signed32(signed_quotient)
        remainder = signed32(make_signed(a) - (signed_quotient * make_signed(b)))
    else:
        quotient = signed32(a // b)
        remainder = signed32(a % b)

    return quotient, remainder

if __name__ == "__main__":
    print(" ".join(sys.argv))

    parser = argparse.ArgumentParser()
    parser.add_argument("-p", "--prints", action="store_true")
    parser.add_argument("-m", "--mine", action="store_true")
    parser.add_argument("-r", "--regression", action="store_true")
    parser.add_argument("-e", "--expected", action="store_true")
    args = parser.parse_args()
    PRINTS = args.prints

    testcases = list()

    if args.mine:
        testcases.append((14, 3, True))
        testcases.append((24, 4, True))
        testcases.append((13, 5, True))
        testcases.append((2, 15, True))
        testcases.append((0, 5, True))
        testcases.append((5, 0, True))

        testcases.append((-17, -6, True))
        testcases.append((-17, -6, False))
        testcases.append((-5, 2, True))
        testcases.append((-5, 2, False))
        testcases.append((24, -7, True))
        testcases.append((24, -7, False))
        testcases.append((-4, -13, True))
        testcases.append((-4, -13, False))
        testcases.append((-3, 9, True))
        testcases.append((-3, 9, False))
        testcases.append((11, -12, True))
        testcases.append((11, -12, False))
        testcases.append((441, 441, False))
        testcases.append((55, -55, False))
        testcases.append((-3, 3, False))
        testcases.append((-170, -170, False))

        testcases.append((0x80000000, -1, True))
        testcases.append((0x80000000, -1, False))
        testcases.append((1234, 0, True))
        testcases.append((1234, 0, False))
        testcases.append((-855, 0, True))
        testcases.append((-855, 0, False))

    if args.regression:
        for i in range(20):
            testcases.append((random.randint(0, 0xFFFFFFFF), random.randint(0, 0xFFFFFFFF), random.randint(0, 1)))
            testcases.append((random.randint(0, 0xFFFFFFFF), random.randint(-0xFFFF, 0xFFFF), random.randint(0, 1)))
            testcases.append((random.randint(-0xFF, 0xFF), random.randint(-0xF, 0xF), random.randint(0, 1)))

    if args.expected:

        dividend_size_percent5 = 0
        dividend_size_percent25 = 0
        dividend_size_percent30 = 0
        dividend_size_percent40 = 0
        
        divisor_size_percent30 = 0
        divisor_size_percent12 = 0
        divisor_size_percent25 = 0
        divisor_size_percent20 = 0
        divisor_size_percent10 = 0
        divisor_size_percent3 = 0
        
        for i in range(1024):
            signed_vs_unsigned = random.randint(1, 100)
            # 70% signed
            if 1 <= signed_vs_unsigned <= 70:
                signed = True
            # 30% unsigned
            else:
                signed = False

            dividend_size = random.randint(1, 100)
            # 5% 0
            if 1 <= dividend_size <= 5:
                a = 0
                dividend_size_percent5 += 1
            # 25% 1:255
            elif 6 <= dividend_size <= 30:
                a = random.randint(1, 255)
                dividend_size_percent25 += 1
            # 30% 256:65535
            elif 31 <= dividend_size <= 60:
                a = random.randint(256, 65535)
                dividend_size_percent30 += 1
            # 40% 65536:2**31-1
            else:
                a = random.randint(65536, 2**31-1)
                dividend_size_percent40 += 1

            dividend_neg_vs_pos = random.randint(1, 100)
            # 45% neg
            if 1 <= dividend_neg_vs_pos <= 45:
                a = -a

            divisor_size = random.randint(1, 100)
            # 30% 1
            if 1 <= divisor_size <= 30:
                b = 1
                divisor_size_percent30 += 1
            # 12% 2
            elif 31 <= divisor_size <= 42:
                b = 2
                divisor_size_percent12 += 1
            # 25% 3:9
            elif 43 <= divisor_size <= 67:
                b = random.randint(3, 9)
                divisor_size_percent25 += 1
            # 20% 10:255
            elif 68 <= divisor_size <= 87:
                b = random.randint(10, 255)
                divisor_size_percent20 += 1
            # 10% 256:65535
            elif 88 <= divisor_size <= 97:
                b = random.randint(256, 65535)
                divisor_size_percent10 += 1
            # 3% 65536:2**31-1
            else:
                b = random.randint(65536, 2**31-1)
                divisor_size_percent3 += 1

            divisor_neg_vs_pos = random.randint(1, 100)
            # 10% neg
            if 1 <= dividend_neg_vs_pos <= 10:
                b = -b

            testcases.append((a, b, signed))

    errors = 0
    for testcase in testcases:
        a = signed32(testcase[0])
        b = signed32(testcase[1])

        # nonrestoring_quo, nonrestoring_rem = div_nonrestoring(a, b, testcase[2])
        nonrestoring_quo, nonrestoring_rem = div_nonrestoring_skip(a, b, testcase[2])
        golden_quo, golden_rem = div_golden(a, b, testcase[2])

        if testcase[2]:
            print(f"{make_signed(a)} / {make_signed(b)} = {make_signed(golden_quo)} R {make_signed(golden_rem)}")
            if nonrestoring_quo != golden_quo or nonrestoring_rem != golden_rem:
                print(f"    ERROR: nonrestoring_quo = {make_signed(nonrestoring_quo)}")
                print(f"    ERROR: nonrestoring_rem = {make_signed(nonrestoring_rem)}")
                errors += 1
        else:
            print(f"{a} / {b} = {golden_quo} R {golden_rem}")
            if nonrestoring_quo != golden_quo or nonrestoring_rem != golden_rem:
                print(f"    ERROR: nonrestoring_quo = {nonrestoring_quo}")
                print(f"    ERROR: nonrestoring_rem = {nonrestoring_rem}")
                errors += 1

    if args.expected:
        print()
        print(f"distributions:")
        print()
        print(f"    dividend_size_percent5 = {dividend_size_percent5 / 1024}")
        print(f"    dividend_size_percent25 = {dividend_size_percent25 / 1024}")
        print(f"    dividend_size_percent30 = {dividend_size_percent30 / 1024}")
        print(f"    dividend_size_percent40 = {dividend_size_percent40 / 1024}")
        print()
        print(f"    divisor_size_percent30 = {divisor_size_percent30 / 1024}")
        print(f"    divisor_size_percent12 = {divisor_size_percent12 / 1024}")
        print(f"    divisor_size_percent25 = {divisor_size_percent25 / 1024}")
        print(f"    divisor_size_percent20 = {divisor_size_percent20 / 1024}")
        print(f"    divisor_size_percent10 = {divisor_size_percent10 / 1024}")
        print(f"    divisor_size_percent3 = {divisor_size_percent3 / 1024}")

    print()
    print(f"avg iters = {ITERS / len(testcases)}")

    print()
    if errors:
        print(f"{errors} / {len(testcases)} testcases failing")
    else:
        print(f"all {len(testcases)} testcases passing")