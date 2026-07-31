#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Ported from lowRISC/opentitan/util/design/sparse-fsm-encode.py
# Self-contained version for Caliptra (no OpenTitan tree dependencies).
r"""Generate sparse FSM encodings that fulfill a minimum Hamming distance
requirement. Uses a heuristic that incrementally draws random state encodings
until a solution has been found.

The Hamming distance d should be set to 3 at minimum. A value of 5 is
recommended for security-critical FSMs in Caliptra.

Usage examples:
  # DOE FSM: 7 states (6 + ERROR), 10-bit encoding, min HD=5
  python3 sparse_fsm_encode.py -d 5 -m 7 -n 10 -s 31415926

  # Mailbox FSM: 7 states (6 + ERROR), 10-bit encoding, min HD=5
  python3 sparse_fsm_encode.py -d 5 -m 7 -n 10 -s 27182818
"""
import argparse
import logging as log
import random
import sys
import textwrap

MAX_DRAWS = 10000
MAX_RESTARTS = 10000


def get_hd(word1, word2):
    """Calculate Hamming distance between two binary strings."""
    if len(word1) != len(word2):
        raise RuntimeError('Words are not of equal size')
    return bin(int(word1, 2) ^ int(word2, 2)).count('1')


def hd_histogram(existing_words):
    """Build Hamming distance histogram."""
    minimum_hd = len(existing_words[0])
    maximum_hd = 0
    minimum_hw = len(existing_words[0])
    maximum_hw = 0
    hist = [0] * (len(existing_words[0]) + 1)
    for i, word1 in enumerate(existing_words):
        hw = word1.count('1')
        minimum_hw = min(minimum_hw, hw)
        maximum_hw = max(maximum_hw, hw)
        for j, word2 in enumerate(existing_words):
            if i < j:
                hd = get_hd(word1, word2)
                hist[hd] += 1
                minimum_hd = min(minimum_hd, hd)
                maximum_hd = max(maximum_hd, hd)

    bars = []
    max_hist = max(hist) if max(hist) > 0 else 1
    for i, count in enumerate(hist):
        if count > 0:
            bar = "{:2d}: ".format(i)
            bar += "|" * (count * 20 // max_hist)
            bar += " ({:.2f}%)".format(100.0 * count / sum(hist))
            bars.append(bar)

    return {
        'min_hd': minimum_hd,
        'max_hd': maximum_hd,
        'min_hw': minimum_hw,
        'max_hw': maximum_hw,
        'bars': bars
    }


def generate_encodings(min_hd, num_states, encoding_len, seed, avoid_zero=True):
    """Generate sparse encodings with minimum Hamming distance."""
    encodings = []
    min_popcnt = min_hd if avoid_zero else 1
    num_draws = 0
    num_restarts = 0

    rng = random.Random()
    rng.seed(seed, version=2)

    while len(encodings) < num_states:
        if num_draws >= MAX_DRAWS:
            num_draws = 0
            num_restarts += 1
            encodings = []
        if num_restarts >= MAX_RESTARTS:
            log.error(
                f'Did not find a solution after {num_restarts} restarts. '
                'Try increasing -n (encoding width) or decreasing -d (distance).')
            sys.exit(1)
        num_draws += 1

        rnd = rng.getrandbits(encoding_len)
        cand = format(rnd, '0' + str(encoding_len) + 'b')

        # Check candidate validity
        pop_cnt = cand.count('1')
        if pop_cnt >= encoding_len or pop_cnt < min_popcnt:
            continue

        valid = True
        for existing in encodings:
            # Disallow complements
            if int(cand, 2) ^ ((1 << encoding_len) - 1) == int(existing, 2):
                valid = False
                break
            # Disallow too-close states
            if get_hd(cand, existing) < min_hd:
                valid = False
                break

        if valid:
            encodings.append(cand)

    return encodings


def print_sv_output(encodings, encoding_len, num_states, min_hd, seed,
                    state_names=None):
    """Print SystemVerilog enum and FSM template."""
    stats = hd_histogram(encodings)

    # Print generation comment for reproducibility
    print(f"// Encoding generated with")
    print(f"// $ python3 sparse_fsm_encode.py -d {min_hd} -m {num_states} "
          f"-n {encoding_len} -s {seed}")
    print(f"//")
    print(f"// Hamming distance histogram:")
    for bar in stats['bars']:
        print(f"//  {bar}")
    print(f"//")
    print(f"// Minimum Hamming distance: {stats['min_hd']}")
    print(f"// Maximum Hamming distance: {stats['max_hd']}")
    print(f"// Minimum Hamming weight: {stats['min_hw']}")
    print(f"// Maximum Hamming weight: {stats['max_hw']}")
    print(f"//")

    # Print localparam and enum
    print(f"localparam int StateWidth = {encoding_len};")
    print(f"typedef enum logic [StateWidth-1:0] {{")

    if state_names and len(state_names) == num_states:
        names = state_names
    else:
        names = [f"State{j}" for j in range(num_states)]

    max_name_len = max(len(n) for n in names)
    for j, (name, enc) in enumerate(zip(names, encodings)):
        comma = "," if j < num_states - 1 else ""
        pad = " " * (max_name_len - len(name))
        print(f"  {name} {pad}= {encoding_len}'b{enc}{comma}")

    print("} state_e;")
    print("")
    print("state_e state_d, state_q;")
    print("")
    print("`CALIPTRA_PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, "
          "state_e, " + names[0] + ")")


def main():
    log.basicConfig(level=log.INFO, format="%(levelname)s: %(message)s")

    parser = argparse.ArgumentParser(
        prog="sparse_fsm_encode",
        description=textwrap.dedent(__doc__),
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument(
        '-d', '--distance',
        type=int, default=5,
        help='Minimum Hamming distance between encoded states (default: 5).')
    parser.add_argument(
        '-m', '--states',
        type=int, default=7,
        help='Number of states to encode (default: 7).')
    parser.add_argument(
        '-n', '--bits',
        type=int, default=10,
        help='Encoding length in bits (default: 10).')
    parser.add_argument(
        '-s', '--seed',
        type=int, default=None,
        help='Custom seed for RNG (default: random).')
    parser.add_argument(
        '--names',
        type=str, default=None,
        help='Comma-separated state names (e.g., "IDLE,LOAD,COMPUTE,DONE,ERROR").')
    parser.add_argument(
        '--avoid-zero',
        dest='avoid_zero', action='store_true', default=True,
        help='Enforce minimum HD from zero word (default: enabled).')
    parser.add_argument(
        '--no-avoid-zero',
        dest='avoid_zero', action='store_false',
        help='Disable the minimum-HD-from-zero constraint (allow encodings near the all-zero word).')

    args = parser.parse_args()

    if args.states < 2:
        log.error('Number of states must be at least 2.')
        sys.exit(1)

    if args.states > 2**args.bits:
        log.error(f'State space 2^{args.bits} cannot fit {args.states} states.')
        sys.exit(1)

    if args.distance >= args.bits:
        log.error(f'Encoding width {args.bits} too small for HD={args.distance}.')
        sys.exit(1)

    if args.distance < 3:
        log.warning('HD < 3 is not recommended for security FSMs.')

    if args.seed is None:
        random.seed()
        args.seed = random.getrandbits(32)

    state_names = None
    if args.names:
        state_names = [n.strip() for n in args.names.split(',')]
        if len(state_names) != args.states:
            log.error(f'--names has {len(state_names)} entries but -m is {args.states}.')
            sys.exit(1)

    encodings = generate_encodings(
        min_hd=args.distance,
        num_states=args.states,
        encoding_len=args.bits,
        seed=args.seed,
        avoid_zero=args.avoid_zero)

    print_sv_output(encodings, args.bits, args.states, args.distance,
                    args.seed, state_names)


if __name__ == "__main__":
    main()
