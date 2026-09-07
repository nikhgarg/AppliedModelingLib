"""Runtime authority type shared by semantic-reuse producers and consumers."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping


@dataclass(frozen=True)
class CurrentSemanticReuseAuthority:
    """One exact-input, declaration-level semantic validation result.

    The verifier issues this runtime object only after rebinding its persisted
    machine result to the current canonical raw rows and every repository input
    watched by the successful Lean pass.  Keeping the nominal authority type in
    this dependency-neutral module prevents evidence consumers from importing
    the verifier implementation (and therefore prevents circular code-identity
    slices) while retaining the exact ``isinstance`` check.
    """

    paper: str
    raw_audit_file_sha256: str
    semantic_identity_sha256: str
    reviewed_declarations: tuple[str, ...]
    watched_repository_material: tuple[tuple[str, str, str], ...]
    result: Mapping[str, Any]
