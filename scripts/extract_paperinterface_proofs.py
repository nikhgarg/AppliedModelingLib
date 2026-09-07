#!/usr/bin/env python3
"""Move Lean-owned PaperInterface proof declarations into ProofInterface.

The current protocol keeps transparent source-semantic ``Spec`` declarations
in ``PaperInterface.lean`` and proof declarations in ``ProofInterface.lean``.
This migration tool deliberately obtains every moved declaration's kind, owning
module, and complete source range from Lean's declaration inventory. Python
uses those ranges only to relocate already-elaborated theorem text; it does not
discover, parse, or classify Lean declarations.
"""

from __future__ import annotations

import argparse
import sys
from collections.abc import Iterable, Mapping
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.current_closeout.lean_review_graph import paper_module_names_from_sources
from scripts.lean_signature_manifest import (
    RepositoryBuildInputSnapshotProvider,
    run_lean_declaration_inventory,
)

PROOF_KINDS = frozenset({"theorem", "lemma"})
ENDPOINT_MARKER = "/-! ## Current source-ledger proof endpoints -/"


class ProofExtractionError(ValueError):
    """The exact Lean-owned extraction plan is unavailable or unsafe."""


@dataclass(frozen=True)
class ProofBlock:
    qualified_name: str
    line_start: int
    line_end: int


def _line_range(raw: object, *, name: str) -> tuple[int, int]:
    if not isinstance(raw, Mapping):
        raise ProofExtractionError(f"{name} has no Lean-owned source range")
    start = raw.get("line_start")
    end = raw.get("line_end")
    if (
        not isinstance(start, int)
        or isinstance(start, bool)
        or not isinstance(end, int)
        or isinstance(end, bool)
        or start < 1
        or end < start
    ):
        raise ProofExtractionError(f"{name} has an invalid Lean-owned source range")
    return start, end


def proof_blocks_from_lean_inventory(
    inventory: object,
    *,
    paper: str,
) -> tuple[ProofBlock, ...]:
    """Select only Lean-owned theorem/lemma declarations in PaperInterface."""

    if not isinstance(inventory, Mapping):
        raise ProofExtractionError("Lean declaration inventory is unavailable")
    raw_declarations = inventory.get("declarations")
    if not isinstance(raw_declarations, list):
        raise ProofExtractionError("Lean declaration inventory has no declarations")
    interface_module = f"{paper}.PaperInterface"
    blocks: list[ProofBlock] = []
    for raw in raw_declarations:
        if not isinstance(raw, Mapping):
            continue
        if raw.get("module") != interface_module:
            continue
        if raw.get("declaration_kind") not in PROOF_KINDS:
            continue
        if raw.get("paper_owned") is not True or raw.get("source_presented") is not True:
            continue
        if raw.get("generated_from_owner") is not False:
            continue
        qualified = str(raw.get("declaration") or "").strip()
        # A Lean module and namespace are independent.  Older PaperInterface
        # files commonly declare ``Paper.result`` directly rather than
        # ``Paper.PaperInterface.result``.  Lean owns both the module and the
        # qualified declaration here; accept either paper-owned namespace and
        # preserve the exact namespace during relocation.
        if not qualified.startswith(paper + "."):
            raise ProofExtractionError("Lean inventory returned a non-paper interface name")
        start, end = _line_range(raw.get("source_range"), name=qualified)
        blocks.append(ProofBlock(qualified, start, end))
    result = tuple(sorted(blocks, key=lambda block: (block.line_start, block.line_end)))
    if not result:
        raise ProofExtractionError("PaperInterface has no Lean-owned theorem/lemma bodies")
    previous_end = 0
    for block in result:
        if block.line_start <= previous_end:
            raise ProofExtractionError("Lean-owned proof ranges overlap")
        previous_end = block.line_end
    return result


def relocate_proof_blocks(
    interface_text: str,
    proof_text: str,
    *,
    paper: str,
    blocks: Iterable[ProofBlock],
) -> tuple[str, str]:
    """Render a range-authorized relocation without interpreting Lean text."""

    selected = tuple(blocks)
    interface_lines = interface_text.splitlines(keepends=True)
    if not selected:
        raise ProofExtractionError("no proof blocks were selected")
    if any(block.line_end > len(interface_lines) for block in selected):
        raise ProofExtractionError("Lean-owned proof range exceeds PaperInterface")
    retained = list(interface_lines)
    moved: list[str] = []
    for block in reversed(selected):
        start = block.line_start - 1
        end = block.line_end
        moved.append("".join(retained[start:end]))
        del retained[start:end]
    moved.reverse()
    marker_count = proof_text.count(ENDPOINT_MARKER)
    if marker_count > 1:
        raise ProofExtractionError(
            "ProofInterface must contain exactly one current-endpoint marker"
        )
    # Legacy ProofInterface files predate the source-ledger marker.  Adding
    # one at EOF is a mechanical migration: it neither selects declarations
    # nor changes their bodies, and it gives subsequent extractions one stable
    # insertion point.
    if marker_count == 0:
        proof_text = proof_text.rstrip() + "\n\n" + ENDPOINT_MARKER + "\n"
    owners = {block.qualified_name.rsplit(".", 1)[0] for block in selected}
    if len(owners) != 1:
        raise ProofExtractionError(
            "Lean-owned proof declarations do not share one namespace"
        )
    owner_namespace = owners.pop()
    if owner_namespace != paper and not owner_namespace.startswith(paper + "."):
        raise ProofExtractionError("Lean inventory returned a non-paper proof namespace")
    owner_parts = owner_namespace.split(".")
    if owner_parts[0] != paper:
        raise ProofExtractionError("Lean inventory returned a malformed proof namespace")
    nested_parts = owner_parts[1:]
    opening_namespaces = ["namespace " + paper]
    closing_namespaces: list[str] = []
    for part in nested_parts:
        opening_namespaces.append("namespace " + part)
        closing_namespaces.append("end " + part)
    namespace = "\n".join(
        [
            *opening_namespaces,
            "",
            "noncomputable section",
            "",
            "open AppliedModelingLib",
            "open AppliedModelingLib.Probability",
            "open MeasureTheory",
            "open ProbabilityTheory",
            "",
            "".join(moved).rstrip(),
            "",
            # The noncomputable section is an unnamed scope nested inside the
            # declaration namespace.  Close it before closing the namespace;
            # the reverse order produces invalid Lean after an otherwise
            # range-authorized relocation.
            "end",
            "",
            *closing_namespaces,
            "",
            "end " + paper,
            "",
        ]
    )
    marker_index = proof_text.index(ENDPOINT_MARKER)
    relocated_proof = proof_text[:marker_index] + namespace + proof_text[marker_index:]
    return "".join(retained), relocated_proof


def extraction_plan(root: Path, paper: str) -> tuple[Path, Path, tuple[ProofBlock, ...]]:
    """Ask Lean once for the exact PaperInterface theorem/lemma ranges."""

    paper_dir = root / "papers" / paper
    interface_path = paper_dir / "PaperInterface.lean"
    proof_path = paper_dir / "ProofInterface.lean"
    if not interface_path.is_file() or not proof_path.is_file():
        raise ProofExtractionError("paper needs PaperInterface.lean and ProofInterface.lean")
    provider = RepositoryBuildInputSnapshotProvider(root)
    snapshots = provider.repository_source_snapshot(f"{paper}.ProofInterface")
    source_modules = {
        module: (path, content) for module, path, content, _digest in snapshots
    }
    if not source_modules:
        raise ProofExtractionError("Lean-owned import closure is unavailable")
    paper_modules = paper_module_names_from_sources(
        root,
        paper_dir,
        source_modules,
        required_entry_module=f"{paper}.ProofInterface",
    )
    inventory = run_lean_declaration_inventory(
        root,
        f"{paper}.ProofInterface",
        inventory_modules=(f"{paper}.PaperInterface",),
        paper_modules=paper_modules,
        workspace_module_names=tuple(source_modules),
        include_semantic_displays=False,
        include_axiom_closure=False,
        timeout_seconds=180,
        build_timeout_seconds=600,
        build_input_provider=provider,
        require_build=True,
    )
    return interface_path, proof_path, proof_blocks_from_lean_inventory(
        inventory, paper=paper
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    paper = args.paper.strip()
    if not paper or Path(paper).name != paper:
        parser.error("--paper must be one paper-directory name")
    try:
        interface_path, proof_path, blocks = extraction_plan(ROOT, paper)
        if not args.write:
            print(
                f"{paper}: Lean selected {len(blocks)} PaperInterface theorem/lemma "
                "declaration(s); rerun with --write"
            )
            return 0
        interface_text = interface_path.read_text(encoding="utf-8")
        proof_text = proof_path.read_text(encoding="utf-8")
        rewritten_interface, rewritten_proof = relocate_proof_blocks(
            interface_text,
            proof_text,
            paper=paper,
            blocks=blocks,
        )
        interface_path.write_text(rewritten_interface, encoding="utf-8")
        proof_path.write_text(rewritten_proof, encoding="utf-8")
    except (OSError, ProofExtractionError) as exc:
        print(f"paper-interface-proof-extraction: {exc}")
        return 1
    print(f"{paper}: moved {len(blocks)} Lean-owned proof declaration(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
