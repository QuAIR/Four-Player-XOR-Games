#!/usr/bin/env python3
"""Check the incidence and parity certificate for the Klein XOR game."""

from __future__ import annotations

import json
from pathlib import Path


INSTANCE = Path(__file__).resolve().parents[1] / "instances" / "klein_v4.json"


def main() -> int:
    game = json.loads(INSTANCE.read_text())
    clauses = game["clauses"]
    players = game["players"]
    questions = game["question_labels"]
    pref = game["pref"]

    if len(clauses) != 8 or len({clause["name"] for clause in clauses}) != 8:
        raise SystemExit("FAIL: expected eight distinct clauses")

    coefficient = {
        clause["name"]: pref[clause["name"][0]] for clause in clauses
    }
    for player_index, player in enumerate(players):
        for question in questions:
            balance = sum(
                coefficient[clause["name"]]
                for clause in clauses
                if clause["questions"][player_index] == question
            )
            if balance != 0:
                raise SystemExit(
                    f"FAIL: incidence balance is {balance} for ({player}, {question})"
                )

    target_pairing = sum(
        coefficient[clause["name"]] * clause["target"] for clause in clauses
    )
    if target_pairing % 2 != 1:
        raise SystemExit(f"FAIL: target pairing is even ({target_pairing})")

    odd_targets = [clause["name"] for clause in clauses if clause["target"] == 1]
    if odd_targets != ["O_0"]:
        raise SystemExit(f"FAIL: unexpected odd targets {odd_targets}")

    print("PASS: A^T z = 0 and b^T z = 1 (mod 2) for the Klein game")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
