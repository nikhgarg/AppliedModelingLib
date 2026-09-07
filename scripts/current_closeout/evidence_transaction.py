"""Exact current-v11 evidence input acquisition, independent of legacy lanes."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import Any, ClassVar

from scripts.configured_paper_inputs import (
    configured_source_proof_fidelity_ledger_path,
    current_v11_canonical_transaction_input_paths,
    current_v11_transaction_input_paths,
)
from scripts.current_closeout.protocol_selection import current_v11_protocol_selected
from scripts.evidence_run_context import (
    CommonEvidenceRunContextInputs,
    EvidenceInputSnapshotTransaction,
    EvidenceJSONSnapshot,
    V11EvidenceRunContext,
)


@dataclass(frozen=True)
class CurrentV11EvidenceSnapshotRoot:
    """Common exact inputs and current-protocol selection for one paper."""

    allow_noncanonical_legacy_folder: ClassVar[bool] = False

    repository_root: Path
    folder: Path
    transaction: EvidenceInputSnapshotTransaction
    status_snapshot: EvidenceJSONSnapshot
    audit_config_snapshot: EvidenceJSONSnapshot
    status: str
    statement_map_path: Path
    statement_map_snapshot: EvidenceJSONSnapshot
    source_proof_fidelity_snapshot: EvidenceJSONSnapshot | None
    source_proof_fidelity_path_error: str
    review_surface: Mapping[str, Any] | None
    v11_selected: bool

    @classmethod
    def acquire(
        cls,
        folder: Path,
        *,
        repository_root: Path,
    ) -> CurrentV11EvidenceSnapshotRoot:
        """Acquire the exact current inputs once without opening legacy state."""

        root = repository_root.resolve()
        paper_folder = folder.resolve()
        expected_folder = (root / "papers" / folder.name).resolve()
        canonical_paper_folder = paper_folder == expected_folder
        if (
            not canonical_paper_folder
            and not cls.allow_noncanonical_legacy_folder
        ):
            raise ValueError("current evidence folder is outside the papers root")

        transaction = EvidenceInputSnapshotTransaction(paper_folder)
        status_snapshot = transaction.snapshot(paper_folder / "status.json")
        audit_config_snapshot = transaction.snapshot(
            root / "papers" / "audit_config.json"
        )
        organized_statement_map_path = (
            paper_folder / "audit" / "paper_statement_map.json"
        )
        organized_statement_map_snapshot = transaction.snapshot(
            organized_statement_map_path
        )
        status_payload = status_snapshot.payload or {}
        status = str(status_payload.get("status") or "").strip().lower()
        v11_selected = current_v11_protocol_selected(
            status_payload,
            organized_statement_map_snapshot.payload,
        )
        if v11_selected and not canonical_paper_folder:
            raise ValueError("current evidence folder is outside the papers root")
        if v11_selected or organized_statement_map_snapshot.sha256 is not None:
            statement_map_path = organized_statement_map_path
            statement_map_snapshot = organized_statement_map_snapshot
        else:
            statement_map_path = paper_folder / "paper_statement_map.json"
            statement_map_snapshot = transaction.snapshot(statement_map_path)

        ledger_path, ledger_error = configured_source_proof_fidelity_ledger_path(
            paper_folder,
            status_payload,
            repository_root=root,
        )
        ledger_snapshot = (
            transaction.snapshot(ledger_path) if ledger_path is not None else None
        )

        if v11_selected:
            selected_paths = current_v11_canonical_transaction_input_paths(
                paper_folder,
                repository_root=root,
            )
            if isinstance(status_snapshot.raw_bytes, bytes):
                try:
                    selected_paths = current_v11_transaction_input_paths(
                        paper_folder,
                        status_bytes=status_snapshot.raw_bytes,
                        statement_map_bytes=statement_map_snapshot.raw_bytes,
                        source_proof_fidelity_bytes=(
                            ledger_snapshot.raw_bytes
                            if ledger_snapshot is not None
                            else None
                        ),
                        repository_root=root,
                    )
                except (OSError, RuntimeError, ValueError):
                    pass
            for path in selected_paths:
                transaction.snapshot(path)

        raw_review_surface = status_payload.get("review_surface")

        return cls(
            repository_root=root,
            folder=paper_folder,
            transaction=transaction,
            status_snapshot=status_snapshot,
            audit_config_snapshot=audit_config_snapshot,
            status=status,
            statement_map_path=statement_map_path,
            statement_map_snapshot=statement_map_snapshot,
            source_proof_fidelity_snapshot=ledger_snapshot,
            source_proof_fidelity_path_error=ledger_error,
            review_surface=(
                raw_review_surface
                if isinstance(raw_review_surface, Mapping)
                else None
            ),
            v11_selected=v11_selected,
        )

    @property
    def status_payload(self) -> dict[str, Any]:
        return self.status_snapshot.payload or {}

    def build_v11(
        self,
        graph_reference: Mapping[str, object] | None,
    ) -> V11EvidenceRunContext:
        """Issue one current context, optionally binding an exact graph object."""

        graph_snapshot: EvidenceJSONSnapshot | None = None
        if graph_reference is not None:
            try:
                from scripts.closeout_content_store import (
                    CloseoutContentStoreError,
                    load_closeout_object,
                )

                loaded_graph = load_closeout_object(
                    self.repository_root,
                    graph_reference,
                    expected_kind="v11_lean_review_graph",
                )
                raw_path = graph_reference.get("path")
                if not isinstance(raw_path, str):
                    raise TypeError("v11 Lean review graph reference has no path")
                graph_snapshot = self.transaction.snapshot(
                    self.repository_root / raw_path
                )
                if graph_snapshot.payload != loaded_graph:
                    raise ValueError(
                        "v11 Lean review graph bytes disagree with their content "
                        "reference"
                    )
            except (
                CloseoutContentStoreError,
                OSError,
                RuntimeError,
                TypeError,
                ValueError,
            ) as exc:
                raise ValueError(
                    "could not acquire the plan-bound v11 Lean review graph: "
                    + str(exc)
                ) from exc

        return self._common_context(
            protocol_core_snapshots=(graph_snapshot,)
        ).issue_v11(graph_snapshot)

    def build_v11_with_graph_checkpoint(self) -> V11EvidenceRunContext:
        """Bind an exact retained graph without reacquiring transaction inputs."""

        from scripts.current_closeout import lean_review_graph

        context = self.build_v11(None)
        try:
            reference = lean_review_graph.current_v11_lean_review_graph_checkpoint_reference(
                self.folder, context, repository_root=self.repository_root,
            )
            if reference is not None:
                return self.build_v11(reference)
        except (OSError, RuntimeError, TypeError, ValueError):
            # A stale/missing cache does not authorize acquisition by this reader.
            pass
        return context

    def _common_context(
        self,
        *,
        protocol_core_snapshots: tuple[EvidenceJSONSnapshot | None, ...],
    ) -> CommonEvidenceRunContextInputs:
        """Freeze common inputs for one selected protocol subtype."""

        sidecars = self.transaction.noncore_snapshots(
            (
                self.status_snapshot,
                self.audit_config_snapshot,
                self.statement_map_snapshot,
                self.source_proof_fidelity_snapshot,
                *protocol_core_snapshots,
            )
        )
        return CommonEvidenceRunContextInputs(
            folder=self.folder,
            status=self.status,
            audit_config_snapshot=self.audit_config_snapshot,
            status_snapshot=self.status_snapshot,
            statement_map_snapshot=self.statement_map_snapshot,
            source_proof_fidelity_snapshot=self.source_proof_fidelity_snapshot,
            sidecar_snapshots=sidecars,
            source_proof_fidelity_path_error=(
                self.source_proof_fidelity_path_error
            ),
        )


def build_current_v11_evidence_run_context(
    folder: Path,
    *,
    repository_root: Path,
    graph_reference: Mapping[str, object] | None = None,
) -> V11EvidenceRunContext:
    """Build one exact current context and reject a non-current paper."""

    root = CurrentV11EvidenceSnapshotRoot.acquire(
        folder,
        repository_root=repository_root,
    )
    if not root.v11_selected:
        raise ValueError("paper does not select the v11 Lean claim-graph protocol")
    return root.build_v11(graph_reference)


def build_current_v11_context_with_graph_checkpoint(
    folder: Path,
    *,
    repository_root: Path,
) -> V11EvidenceRunContext:
    """Reuse a current graph checkpoint without reacquiring transaction files."""

    root = CurrentV11EvidenceSnapshotRoot.acquire(
        folder,
        repository_root=repository_root,
    )
    if not root.v11_selected:
        raise ValueError("paper does not select the v11 Lean claim-graph protocol")
    return root.build_v11_with_graph_checkpoint()
