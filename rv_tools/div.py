from iss import bits, bit, signed32, make_signed

PRINTS = True

def div_nonrestoring(a, b, signed):
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
    # must "sign-extend" (not real sign-extend as technically still unsigned)
    if bit(a_abs, 31):
        AQ += 0xFFFFFFFF00000000
    # print(f"         init AQ = 0b_{bit(AQ, 64)}_{bits(AQ, 63, 32):032b}_{bits(AQ, 31, 0):032b}") if PRINTS else None
    print(f"         init AQ = 0b_{bits(AQ, 63, 32):032b}_{bits(AQ, 31, 0):032b}") if PRINTS else None

    for iter in range(32):
        # AQ = bits(AQ << 1, 64, 0)
        AQ = bits(AQ << 1, 63, 0)
        # print(f"   post-shift AQ = 0b_{bit(AQ, 64)}_{bits(AQ, 63, 32):032b}_{bits(AQ, 31, 0):032b}") if PRINTS else None
        # print(f"   post-shift AQ = 0b_{bits(AQ, 63, 32):032b}_{bits(AQ, 31, 0):032b}") if PRINTS else None
        # A = bits(AQ, 64, 32)
        A = bits(AQ, 63, 32)
        # if bit(A, 32):
        if bit(A, 31):
            # A = bits(A + b_abs, 32, 0)
            A = bits(A + b_abs, 31, 0)
        else:
            # A = bits(A - b_abs, 32, 0)
            A = bits(A - b_abs, 31, 0)
        # AQ = (A << 32) + (bits(AQ, 31, 1) << 1) + (not bit(A, 32))
        AQ = (A << 32) + (bits(AQ, 31, 1) << 1) + (not bit(A, 31))
        # print(f"after iter {iter:2d} AQ = 0b_{bit(AQ, 64)}_{bits(AQ, 63, 32):032b}_{bits(AQ, 31, 0):032b}") if PRINTS else None
        print(f"after iter {iter:2d} AQ = 0b_{bits(AQ, 63, 32):032b}_{bits(AQ, 31, 0):032b}") if PRINTS else None

    # A = bits(AQ, 64, 32)
    A = bits(AQ, 63, 32)
    # if bit(A, 32):
    if bit(A, 31):
        # A = bits(A + b_abs, 32, 0)
        A = bits(A + b_abs, 31, 0)

    # print(f"        final AQ = 0b_{bit(A, 32)}_{bits(A, 31, 0):032b}_{bits(AQ, 31, 0):032b}") if PRINTS else None
    print(f"        final AQ = 0b_{bits(A, 31, 0):032b}_{bits(AQ, 31, 0):032b}") if PRINTS else None

    quotient = bits(AQ, 31, 0)
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
    testcases = list()

    testcases.append((14, 3, True))
    testcases.append((24, 4, True))
    testcases.append((13, 5, True))
    testcases.append((2, 15, True))
    testcases.append((0, 5, True))
    testcases.append((5, 0, True))

    testcases.append((-17, -6, True))
    testcases.append((-17, -6, False))
    # testcases.append((-5, 2, True))
    # testcases.append((-5, 2, False))
    # testcases.append((24, -7, True))
    # testcases.append((24, -7, False))
    # testcases.append((-4, -13, True))
    # testcases.append((-4, -13, False))
    # testcases.append((-3, 9, True))
    # testcases.append((-3, 9, False))
    # testcases.append((11, -12, True))
    # testcases.append((11, -12, False))

    # testcases.append((0x80000000, -1, True))
    # testcases.append((0x80000000, -1, False))

    for testcase in testcases:
        a = signed32(testcase[0])
        b = signed32(testcase[1])

        nonrestoring_quo, nonrestoring_rem = div_nonrestoring(a, b, testcase[2])
        golden_quo, golden_rem = div_golden(a, b, testcase[2])

        if testcase[2]:
            print(f"{make_signed(a)} / {make_signed(b)} = {make_signed(golden_quo)} R {make_signed(golden_rem)}")
            if nonrestoring_quo != golden_quo:
                print(f"    ERROR: nonrestoring_quo = {make_signed(nonrestoring_quo)}")
            if nonrestoring_rem != golden_rem:
                print(f"    ERROR: nonrestoring_rem = {make_signed(nonrestoring_rem)}")
        else:
            print(f"{a} / {b} = {golden_quo} R {golden_rem}")
            if nonrestoring_quo != golden_quo:
                print(f"    ERROR: nonrestoring_quo = {nonrestoring_quo}")
            if nonrestoring_rem != golden_rem:
                print(f"    ERROR: nonrestoring_rem = {nonrestoring_rem}")