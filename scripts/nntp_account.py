#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""A line of the NNTP server's file of accounts (`--users`, native/accounts.h) for NAME, the password
read from the terminal, or from the first line of standard input when it is not one:
`NAME:ITERATIONS:SALT:KEY`, the key PBKDF2-HMAC-SHA256's (RFC 8018 §5.2) of the password over
sixteen random octets of salt, both in hex. AUTHINFO splits its line at white space, so neither the
name nor the password may hold any."""
from __future__ import annotations

import argparse
import getpass
import hashlib
import os
import sys

# OWASP's count for PBKDF2-HMAC-SHA256 (Password Storage Cheat Sheet), and the bounds the server takes.
ITERATIONS, ITERATIONS_MIN, ITERATIONS_MAX = 600_000, 600_000, 100_000_000
NAME_MAX, PASSWORD_MAX = 64, 256


def line(name: bytes, password: bytes, iterations: int = ITERATIONS, salt: bytes | None = None) -> str:
    """The account's line."""
    if not 1 <= len(name) <= NAME_MAX or any(b < 33 or b > 126 or b == 58 for b in name) or name[:1] == b"#":
        raise ValueError(f"a name of 1 to {NAME_MAX} visible octets other than the colon, not starting with #")
    if not 1 <= len(password) <= PASSWORD_MAX or any(b in b" \t\r\n\0" for b in password):
        raise ValueError(f"a password of 1 to {PASSWORD_MAX} octets and no white space")
    if not ITERATIONS_MIN <= iterations <= ITERATIONS_MAX:
        raise ValueError(f"iterations from {ITERATIONS_MIN} to {ITERATIONS_MAX}")
    salt = os.urandom(16) if salt is None else salt
    key = hashlib.pbkdf2_hmac("sha256", password, salt, iterations, 32)
    return f"{name.decode()}:{iterations}:{salt.hex()}:{key.hex()}"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("name")
    parser.add_argument("--iterations", type=int, default=ITERATIONS)
    args = parser.parse_args()
    if sys.stdin.isatty():
        password = getpass.getpass().encode()
    else:
        password = sys.stdin.buffer.readline().rstrip(b"\r\n")
    try:
        print(line(os.fsencode(args.name), password, args.iterations))
    except ValueError as error:
        sys.exit(f"nntp_account: {error}")


if __name__ == "__main__":
    main()
