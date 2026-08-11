#!/bin/sh
set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/.." && pwd)

cd "$repo_root"
cd "$repo_root/formalization"
lake build FourPlayerXORGames

cd "$repo_root"
python3 -m unittest discover -s tests -v
python3 computations/check_klein_pref.py
python3 computations/check_magnus_certificate.py
python3 computations/check_paircount_identities.py
