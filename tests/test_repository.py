from __future__ import annotations

import json
from pathlib import Path
import re
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]


class PublicRepositoryTest(unittest.TestCase):
    def test_public_surface_is_complete(self) -> None:
        expected = {
            "README.md",
            "LICENSE",
            "NOTICE",
            "CITATION.cff",
            "formalization/README.md",
            "formalization/FORMALIZATION.md",
            "formalization/FourPlayerXORGames.lean",
            "formalization/lakefile.toml",
            "formalization/lake-manifest.json",
            "formalization/lean-toolchain",
            "instances/klein_v4.json",
            "computations/check_klein_pref.py",
            "computations/check_magnus_certificate.py",
            "computations/check_paircount_identities.py",
            "scripts/verify_all.sh",
        }
        missing = sorted(path for path in expected if not (ROOT / path).is_file())
        self.assertEqual(missing, [])

    def test_repository_excludes_manuscript_source_and_rendered_artifacts(self) -> None:
        forbidden_suffixes = {".bib", ".pdf", ".tex"}
        artifacts = sorted(
            path.relative_to(ROOT).as_posix()
            for path in ROOT.rglob("*")
            if path.is_file()
            and ".git" not in path.parts
            and ".lake" not in path.parts
            and path.suffix.lower() in forbidden_suffixes
        )
        self.assertEqual(artifacts, [])
        stale_ignore_patterns = {
            "*.aux",
            "*.bbl",
            "*.blg",
            "*.log",
            "*.out",
            "*.synctex.gz",
            "*.toc",
            "paper/_build/",
        }
        gitignore_patterns = set((ROOT / ".gitignore").read_text().splitlines())
        self.assertEqual(sorted(stale_ignore_patterns & gitignore_patterns), [])

    def test_readme_maps_paper_results_and_emphasizes_qit_import(self) -> None:
        path = ROOT / "README.md"
        self.assertTrue(path.is_file(), "README.md has not been exported")
        readme = path.read_text()
        required = {
            "import QIT",
            "QuAIR/Lean-QIT",
            "thm:main",
            "thm:exact-circuit-lifting",
            "cor:obstruction-exactness",
            "thm:cayley-cyclic",
            "commutingOperatorValue_eq_one_iff_hasPerfectMERP_of_activeQuestionBound_le_three",
            "primitiveCircuit_lifts_fourByThree",
            "obstructionSpaces_eq_fourByThree",
            "hasCommonNoncrossingOrder_iff_isCyclic",
            "cayley_f2r_hasPREF_and_no_refutation",
            "four_is_sharp_threshold",
        }
        self.assertEqual(sorted(item for item in required if item not in readme), [])

    def test_paper_facing_obstruction_wrapper_exists(self) -> None:
        aggregator = (ROOT / "formalization/FourPlayerXORGames.lean").read_text()
        self.assertIn("theorem obstructionSpaces_eq_fourByThree", aggregator)

    def test_single_lake_project_imports_pinned_qit(self) -> None:
        lakefiles = sorted(path for path in ROOT.glob("**/lakefile.toml") if ".lake" not in path.parts)
        toolchains = sorted(path for path in ROOT.glob("**/lean-toolchain") if ".lake" not in path.parts)
        manifests = sorted(path for path in ROOT.glob("**/lake-manifest.json") if ".lake" not in path.parts)
        self.assertEqual(lakefiles, [ROOT / "formalization/lakefile.toml"])
        self.assertEqual(toolchains, [ROOT / "formalization/lean-toolchain"])
        self.assertEqual(manifests, [ROOT / "formalization/lake-manifest.json"])
        lakefile = lakefiles[0].read_text()
        self.assertRegex(lakefile, r'(?s)name\s*=\s*"QIT".*git\s*=.*QuAIR/Lean-QIT')
        self.assertRegex(lakefile, r'rev\s*=\s*"[0-9a-f]{40}"')

    def test_clean_checkout_verification_builds_lean_before_contracts(self) -> None:
        script = (ROOT / "scripts/verify_all.sh").read_text()
        self.assertLess(
            script.index("lake build FourPlayerXORGames"),
            script.index("python3 -m unittest"),
        )
        readme = (ROOT / "README.md").read_text()
        command_block = readme[readme.index("Or run the components separately:") :]
        self.assertLess(
            command_block.index("lake build FourPlayerXORGames"),
            command_block.index("python3 -m unittest"),
        )

    def test_no_internal_workflow_markers_or_local_paths(self) -> None:
        forbidden_insensitive = [
            "mile" + "stone",
            "sub" + "agent",
            "main " + "agent",
            "working " + "plan",
            "hand" + "off",
            "Lean-QIT" + "-Dev",
            "/Users" + "/",
            "/private" + "/" + "t" + "mp/",
            "/t" + "mp/",
        ]
        internal_result_label = re.compile(r"\bTheorem\s+[ABC](?=\b|:)")
        internal_stage_label = re.compile(r"\bM[0-9]+\b")
        allowed_suffixes = {".md", ".tex", ".bib", ".lean", ".toml", ".json", ".py", ".sh", ".yml", ".yaml", ".cff", ""}
        hits: list[str] = []
        for path in ROOT.rglob("*"):
            if (
                not path.is_file()
                or ".git" in path.parts
                or ".lake" in path.parts
                or path.suffix not in allowed_suffixes
            ):
                continue
            if path.resolve() == Path(__file__).resolve():
                continue
            text = path.read_text(errors="replace")
            lowered = text.lower()
            for term in forbidden_insensitive:
                if term.lower() in lowered:
                    hits.append(f"{path.relative_to(ROOT)}:{term}")
            if internal_result_label.search(text):
                hits.append(f"{path.relative_to(ROOT)}:internal result label")
            if internal_stage_label.search(text):
                hits.append(f"{path.relative_to(ROOT)}:internal stage label")
        self.assertEqual(hits, [])

    def test_lean_sources_have_no_placeholders_or_new_axioms(self) -> None:
        forbidden = re.compile(r"\b(sorry|admit|axiom)\b")
        hits: list[str] = []
        packages = ROOT / "formalization" / ".lake" / "packages"
        packages.mkdir(parents=True, exist_ok=True)
        with (
            tempfile.TemporaryDirectory(prefix="ci-dependency-", dir=packages) as temporary,
            tempfile.TemporaryDirectory(prefix="owned-source-", dir=ROOT / "formalization") as owned_temporary,
        ):
            dependency = Path(temporary) / "Dependency.lean"
            dependency.write_text("theorem dependency_placeholder : True := by sorry\n")
            owned_source = Path(owned_temporary) / "OwnedSource.lean"
            owned_source.write_text("theorem owned_placeholder : True := by admit\n")
            for path in (ROOT / "formalization").rglob("*.lean"):
                if ".lake" in path.parts:
                    continue
                if match := forbidden.search(path.read_text()):
                    hits.append(f"{path.relative_to(ROOT)}:{match.group(0)}")
            owned_hit = f"{owned_source.relative_to(ROOT)}:admit"
            self.assertIn(owned_hit, hits)
            hits.remove(owned_hit)
        self.assertEqual(hits, [])

    def test_every_lean_module_is_reachable_from_public_aggregator(self) -> None:
        source_root = ROOT / "formalization"
        aggregator = source_root / "FourPlayerXORGames.lean"
        self.assertTrue(aggregator.is_file(), "public Lean aggregator has not been exported")
        modules = {
            ".".join(path.relative_to(source_root).with_suffix("").parts): path
            for directory in ("XORGameFormalization", "FourXOR")
            for path in (source_root / directory).rglob("*.lean")
        }
        modules["FourPlayerXORGames"] = aggregator
        seen: set[str] = set()
        stack = ["FourPlayerXORGames"]
        while stack:
            module = stack.pop()
            if module in seen:
                continue
            seen.add(module)
            text = modules[module].read_text()
            for imported in re.findall(
                r"(?m)^(?:public\s+)?import\s+([A-Za-z0-9_.]+)", text
            ):
                if imported in modules:
                    stack.append(imported)
        self.assertEqual(sorted(set(modules) - seen), [])

    def test_klein_instance_matches_the_paper_table(self) -> None:
        path = ROOT / "instances/klein_v4.json"
        self.assertTrue(path.is_file(), "Klein instance has not been exported")
        data = json.loads(path.read_text())
        self.assertEqual(data["players"], ["0", "a", "b", "c"])
        self.assertEqual(len(data["clauses"]), 8)
        odd = [clause["name"] for clause in data["clauses"] if clause["target"] == 1]
        self.assertEqual(odd, ["O_0"])
        self.assertEqual(data["pref"], {"E": -1, "O": 1})


class ComputationEntrypointTest(unittest.TestCase):
    def test_exact_computations_pass(self) -> None:
        for script in (
            "check_klein_pref.py",
            "check_magnus_certificate.py",
            "check_paircount_identities.py",
        ):
            result = subprocess.run(
                ["python3", str(ROOT / "computations" / script)],
                cwd=ROOT,
                text=True,
                capture_output=True,
            )
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("PASS", result.stdout)


if __name__ == "__main__":
    unittest.main()
