from __future__ import annotations

from pathlib import Path
import re
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
FORMALIZATION = ROOT / "formalization"

DECLARATIONS = (
    "QIT.XORGame.commutingOperatorValue_eq_one_iff_hasPerfectMERP_of_activeQuestionBound_le_three",
    "QIT.XORGame.primitiveCircuit_lifts_fourByThree",
    "QIT.XORGame.obstructionSpaces_eq_fourByThree",
    "QIT.XORGame.v4_value_one",
    "QIT.XORGame.v4_no_MERP",
    "QIT.XORGame.four_is_sharp_threshold",
    "QIT.Research.FourXOR.hasCommonNoncrossingOrder_iff_isCyclic",
    "QIT.Research.FourXOR.cayley_f2r_hasPREF_and_no_refutation",
)

ALLOWED_AXIOMS = {
    "propext",
    "Classical.choice",
    "Quot.sound",
    "QIT.XORGame.fourByThreeClause_card._native.native_decide.ax_1_1✝",
    "QIT.XORGame.hammingSphere_card_profile._native.native_decide.ax_1_1✝",
    "QIT.XORGame.radiusOneBall_card._native.native_decide.ax_1_1✝",
    "QIT.XORGame.radiusOneBall_inter_card._native.native_decide.ax_1_1✝",
    "QIT.XORGame.mem_ternaryCoset_iff_syndrome._native.native_decide.ax_1_1✝",
    "QIT.XORGame.radiusOneBall_inter_ternaryCoset_card._native.native_decide.ax_1_1✝",
    "QIT.XORGame.ternaryCoset_card._native.native_decide.ax_1_1✝",
}


def parse_axiom_dependencies(output: str) -> list[set[str]]:
    blocks = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output)
    return [
        {token.strip() for token in block.split(",") if token.strip()}
        for block in blocks
    ]


class LeanContractTest(unittest.TestCase):
    def test_every_mapped_declaration_exists(self) -> None:
        mapping = (FORMALIZATION / "FORMALIZATION.md").read_text(encoding="utf-8")
        declarations = sorted(set(re.findall(r"`(QIT\.[A-Za-z0-9_.]+)`", mapping)))
        self.assertGreater(len(declarations), 20)
        source = "import FourPlayerXORGames\n\n" + "\n".join(
            f"#check {declaration}" for declaration in declarations
        )
        with tempfile.TemporaryDirectory(prefix="four-player-xor-mapping-") as directory:
            contract = Path(directory) / "Mapping.lean"
            contract.write_text(source, encoding="utf-8")
            result = subprocess.run(
                ["lake", "env", "lean", str(contract)],
                cwd=FORMALIZATION,
                text=True,
                capture_output=True,
            )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_paper_facing_declarations_and_axiom_dependencies(self) -> None:
        checks = "\n".join(f"#check {declaration}" for declaration in DECLARATIONS)
        audits = "\n".join(f"#print axioms {declaration}" for declaration in DECLARATIONS)
        source = f"import FourPlayerXORGames\n\n{checks}\n\n{audits}\n"
        with tempfile.TemporaryDirectory(prefix="four-player-xor-contract-") as directory:
            contract = Path(directory) / "Contract.lean"
            contract.write_text(source, encoding="utf-8")
            result = subprocess.run(
                ["lake", "env", "lean", str(contract)],
                cwd=FORMALIZATION,
                text=True,
                capture_output=True,
            )
        output = result.stdout + result.stderr
        self.assertEqual(result.returncode, 0, output)
        axiom_sets = parse_axiom_dependencies(output)
        self.assertEqual(len(axiom_sets), len(DECLARATIONS), output)
        for axioms in axiom_sets:
            self.assertTrue(
                axioms.issubset(ALLOWED_AXIOMS),
                f"Unexpected axiom dependencies: {sorted(axioms - ALLOWED_AXIOMS)}",
            )


if __name__ == "__main__":
    unittest.main()
