#!/usr/bin/env python3
"""Lean-native regression for semantic identity across a coherent root rename."""

from __future__ import annotations

import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

from scripts import lean_signature_manifest as manifest

ROOT = Path(__file__).resolve().parents[2]


class NamespaceRelocationSemanticIdentityTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        build = subprocess.run(
            ["lake", "build", "AppliedModelingLib.Audit.SignatureManifest"],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
            timeout=180,
        )
        if build.returncode != 0:
            raise RuntimeError(build.stderr)
        environment = subprocess.run(
            ["lake", "env", "bash", "-lc", 'printf "%s" "$LEAN_PATH"'],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=True,
            timeout=30,
        )
        cls.lean_path = environment.stdout.strip()
        hash_tool = manifest._semantic_contract_closure_hash_tool_identity()
        if hash_tool is None:
            raise RuntimeError("semantic hash tool is unavailable")
        cls.hash_tool_path = str(hash_tool["resolved_path"])

    def _compile_module(
        self,
        root: Path,
        module: str,
        source: str,
    ) -> subprocess.CompletedProcess[str]:
        path = root / (module.replace(".", "/") + ".lean")
        output = path.with_suffix(".olean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")
        environment = dict(os.environ)
        # Put the repository's compiled library first so a relocation fixture
        # that deliberately uses the current project root does not shadow the
        # imported audit helper subtree. Fixture-only modules still resolve
        # from the temporary suffix.
        environment["LEAN_PATH"] = f"{self.lean_path}:{root}"
        result = subprocess.run(
            [
                "lake",
                "env",
                "env",
                f"LEAN_PATH={environment['LEAN_PATH']}",
                "lean",
                "--root",
                str(root),
                "-o",
                str(output),
                str(path),
            ],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
            timeout=120,
        )
        self.assertEqual(
            result.returncode,
            0,
            "stdout:\n" + result.stdout + "\nstderr:\n" + result.stderr,
        )
        return result

    def _manifest(
        self,
        root: Path,
        project_root: str,
        *,
        include_library_module: bool,
        shifted_body: str = "Nat.succ x",
    ) -> dict[str, object]:
        library_module = f"{project_root}.Library"
        paper_module = f"{project_root}.Paper"
        declaration = f"{project_root}.Paper.sourceSpec"
        self._compile_module(
            root,
            library_module,
            f"""namespace {project_root}.Library

def shifted (x : Nat) : Nat := {shifted_body}

end {project_root}.Library
""",
        )
        scope = (
            f"{library_module},{paper_module}"
            if include_library_module
            else paper_module
        )
        result = self._compile_module(
            root,
            paper_module,
            f"""import {library_module}
import AppliedModelingLib.Audit.SignatureManifest

namespace {project_root}.Paper

def sourceSpec (x : Nat) : Prop :=
  {project_root}.Library.shifted x = Nat.succ x

end {project_root}.Paper

#signature_manifest {json.dumps(declaration)} {json.dumps(scope)} {json.dumps(self.hash_tool_path)}
""",
        )
        parsed = manifest.parse_signature_manifest_output(result.stdout)
        self.assertEqual(set(parsed), {declaration}, result.stdout)
        return parsed[declaration]

    def test_workspace_scope_is_stable_across_module_and_namespace_rename(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            old = self._manifest(
                root,
                "FormerProject",
                include_library_module=True,
            )
            new = self._manifest(
                root,
                "RenamedProject",
                include_library_module=True,
            )

        self.assertEqual(old["sha256"], new["sha256"])
        old_claim = manifest.review_claim_atom_surface(old)
        new_claim = manifest.review_claim_atom_surface(new)
        self.assertIsNotNone(old_claim)
        self.assertIsNotNone(new_claim)
        assert old_claim is not None and new_claim is not None
        self.assertEqual(
            old_claim["claim_atoms_sha256"],
            new_claim["claim_atoms_sha256"],
        )

    def test_paper_only_scope_exposes_the_current_rename_churn(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            old = self._manifest(
                root,
                "FormerProject",
                include_library_module=False,
            )
            new = self._manifest(
                root,
                "RenamedProject",
                include_library_module=False,
            )

        self.assertNotEqual(old["sha256"], new["sha256"])

    def test_workspace_scope_rejects_a_changed_imported_definition(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            old = self._manifest(
                root,
                "FormerProject",
                include_library_module=True,
            )
            changed = self._manifest(
                root,
                "RenamedProject",
                include_library_module=True,
                shifted_body="Nat.succ (Nat.succ x)",
            )

        self.assertNotEqual(old["sha256"], changed["sha256"])


if __name__ == "__main__":
    unittest.main()
