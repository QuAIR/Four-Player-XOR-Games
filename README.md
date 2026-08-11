# A Sharp Local-Question Threshold for GHZ-Equatorial Strategies in Four-Player XOR Games

This repository contains the Lean 4 formalization and exact algebraic checks
accompanying the paper *A Sharp Local-Question Threshold for GHZ-Equatorial
Strategies in Four-Player XOR Games*.  The manuscript source and rendered PDF
are distributed separately and are not included here.

The main result identifies four as the smallest active local-question bound at
which a perfect four-player binary XOR game in the commuting-operator model
need not admit a perfect GHZ-equatorial (MERP) strategy.  At most three active
questions per player, commuting-operator value one is equivalent to perfect
MERP satisfiability.  At four questions, an eight-clause Klein four-group game
has commuting-operator value one but inconsistent MERP phase equations.

## Contents

- [`formalization/`](formalization/) contains one Lean project for the results of the paper.
- [`instances/klein_v4.json`](instances/klein_v4.json) is the eight-clause witness in the paper.
- [`computations/`](computations/) contains exact checks of the PREF and Magnus certificates.
- [`scripts/verify_all.sh`](scripts/verify_all.sh) runs the complete reproducibility check.

## Lean-QIT dependency

The formalization does **not** vendor a copy of Lean-QIT.  It imports the public
[`QuAIR/Lean-QIT`](https://github.com/QuAIR/Lean-QIT) library as the Lean package
`QIT` at the commit pinned in [`formalization/lakefile.toml`](formalization/lakefile.toml):

```lean
import QIT
```

```toml
[[require]]
name = "QIT"
git = "https://github.com/QuAIR/Lean-QIT.git"
rev = "bb3ada54fa451996df9e197c2be53c2625bc99a3"
```

`QIT` supplies reusable quantum-information, operator-theoretic, and XOR-game
infrastructure.  The theorem-specific circuit lifting, Hamming geometry,
Cayley matching, Klein witness, and all-length obstruction are maintained in
this repository.  Lean-QIT in turn imports Mathlib.  The tracked Lake manifest
and Lean toolchain make the complete dependency graph reproducible.

## Manuscript-to-Lean correspondence

The following table lists the paper-facing declarations.  A more detailed
statement map is in [`formalization/FORMALIZATION.md`](formalization/FORMALIZATION.md).

| Manuscript result | Principal Lean declaration | Coverage |
|---|---|---|
| `thm:main`, part (i) | `QIT.XORGame.commutingOperatorValue_eq_one_iff_hasPerfectMERP_of_activeQuestionBound_le_three` | Direct |
| `thm:exact-circuit-lifting` | `QIT.XORGame.primitiveCircuit_lifts_fourByThree` | Its parity-lifting consequence is formalized; the stronger exact-multiplicity and alternating-vector statement is not exposed as one Lean theorem |
| `cor:obstruction-exactness` | `QIT.XORGame.obstructionSpaces_eq_fourByThree` | Direct |
| `thm:main`, part (ii) | `QIT.XORGame.v4_value_one`, `QIT.XORGame.v4_no_MERP` | Direct |
| Sharp threshold in `thm:main` | `QIT.XORGame.four_is_sharp_threshold` | Direct |
| `thm:cayley-cyclic` | `QIT.Research.FourXOR.hasCommonNoncrossingOrder_iff_isCyclic` | The matching classification is direct; the stated each-clause-once refutation equivalence is only partially represented |
| Elementary-abelian obstruction in `sec:magnus` | `QIT.Research.FourXOR.cayley_f2r_hasPREF_and_no_refutation` | Direct, through a specialized combinatorial proof |

“Direct” means that the cited declaration states the manuscript conclusion,
up to notation and packaging.  The detailed map distinguishes direct
formalizations from conditional supporting lemmas and application-specific
alternative proof routes; it does not claim that every numbered intermediate
statement has been transcribed verbatim into Lean.

The public entrypoint is
[`formalization/FourPlayerXORGames.lean`](formalization/FourPlayerXORGames.lean).
The Lean sources contain no `sorry`, `admit`, or manually declared axioms.
The automated `#print axioms` contract permits only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`, together with seven explicitly
enumerated `native_decide` bridge axioms used by the finite cardinality and
Hamming-space computations in the three-question proof.  The V4 witness,
finite-group classification, and all-length elementary-abelian obstruction use
only the three standard axioms above.

## Reproduction

Requirements are Python 3, Git, and
[`elan`](https://github.com/leanprover/elan).  The first Lean build needs
network access to fetch the pinned `QIT` dependency.  Mathlib build artifacts
are obtained through its cache rather than rebuilt from source.

Run everything from the repository root:

```bash
sh scripts/verify_all.sh
```

Or run the components separately:

```bash
cd formalization
lake exe cache get
lake build FourPlayerXORGames

cd ..
python3 -m unittest discover -s tests -v
python3 computations/check_klein_pref.py
python3 computations/check_magnus_certificate.py
python3 computations/check_paircount_identities.py
```

The computations use exact integer and rational arithmetic.  They check the
displayed certificates; the all-length mathematical conclusion does not rely
on a finite search over refutation words.

## Scope

The repository contains only material used directly by the manuscript or its
formal verification.  It intentionally omits exploratory searches, draft
proofs, development reports, copied literature, and generated build products.

## Citation

Citation metadata are provided in [`CITATION.cff`](CITATION.cff).  Please also
cite Lean-QIT when using the formal development:

> C. Zhu, Z. Tang, G. Zhen, Y. Cao, Y. Zhao, R. Chen, X. Zhao, L. Zhang, and
> X. Wang, “Lean-QIT: Towards a Formal Infrastructure for Quantum Information
> Theory,” arXiv:2607.09632 (2026).

## License

The code is released under the Apache License 2.0.  See [`LICENSE`](LICENSE)
and [`NOTICE`](NOTICE).  The manuscript remains subject to the authors' and
publisher's applicable publication terms.
