# Exact certificate checks

These scripts reproduce the finite algebra appearing explicitly in the paper.
They are checks of displayed identities, not bounded searches for refutation
words.

- `check_klein_pref.py` verifies the incidence balance and odd target pairing
  of the eight-clause Klein witness.
- `check_magnus_certificate.py` verifies the explicit integer combination of
  the pair-count equations.
- `check_paircount_identities.py` independently rebuilds the pair-count
  identities, checks the certificate, and confirms the parity obstruction by
  exact rational elimination.

All mandatory checks use Python's exact integer and rational arithmetic.

```bash
python3 computations/check_klein_pref.py
python3 computations/check_magnus_certificate.py
python3 computations/check_paircount_identities.py
```
