#!/usr/bin/env python3
"""Load the small, package-level trusted-foundation policy.

This registry prevents a closeout from automatically expanding into semantic
review of every Lean or Mathlib declaration reached by a paper. It is
deliberately *not* an allowlist of individual constants. The exact package
revisions remain pinned by the repository toolchain and dependency lock;
paper-facing occurrences and their elaborated arguments remain visible to the
source-to-Lean review. A reviewer may still promote an unusual material concept
to a bounded recursive semantic expansion.

Workspace libraries are prohibited here. Material declarations from Cslib,
AppliedModelingLib, and paper modules belong to the ordinary reviewed semantic frontier.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path

REGISTRY_RELATIVE_PATH = Path("config/trusted_foundation_packages.json")
REGISTRY_SCHEMA = 1
ARGUMENT_POLICY = "retain_occurrence_and_recursively_scan_elaborated_arguments"
PACKAGE_CATEGORIES = frozenset(
    {"trusted_lean_foundation", "trusted_mathematics_foundation"}
)
SEMANTIC_POLICY = "default_trust_with_reviewable_semantic_expansion"
FORBIDDEN_WORKSPACE_ROOTS = frozenset({"Cslib", "AppliedModelingLib", "papers"})
_MODULE_ROOT = re.compile(r"[A-Z][A-Za-z0-9_']*")


@dataclass(frozen=True)
class FoundationPackage:
    module_root: str
    category: str
    semantic_policy: str

    def transport(self) -> dict[str, str]:
        return {
            "module_root": self.module_root,
            "category": self.category,
            "semantic_policy": self.semantic_policy,
        }


@dataclass(frozen=True)
class FoundationRegistry:
    policy_id: str
    argument_policy: str
    packages: tuple[FoundationPackage, ...]
    sha256: str

    @property
    def module_roots(self) -> tuple[str, ...]:
        return tuple(package.module_root for package in self.packages)

    def transport(self) -> dict[str, object]:
        return {
            "schema": REGISTRY_SCHEMA,
            "policy_id": self.policy_id,
            "argument_policy": self.argument_policy,
            "registry_sha256": self.sha256,
            "packages": [package.transport() for package in self.packages],
        }


def _canonical_payload(
    policy_id: str,
    argument_policy: str,
    packages: tuple[FoundationPackage, ...],
) -> dict[str, object]:
    return {
        "schema": REGISTRY_SCHEMA,
        "policy_id": policy_id,
        "argument_policy": argument_policy,
        "packages": [package.transport() for package in packages],
    }


def load_foundation_registry(root: Path) -> FoundationRegistry:
    """Return the canonical package registry or fail closed with ``ValueError``."""

    path = root / REGISTRY_RELATIVE_PATH
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"could not read trusted-foundation registry: {exc}") from exc
    if not isinstance(raw, dict) or set(raw) != {
        "schema",
        "policy_id",
        "argument_policy",
        "packages",
    }:
        raise ValueError("trusted-foundation registry has an unexpected shape")
    policy_id = str(raw.get("policy_id") or "").strip()
    argument_policy = str(raw.get("argument_policy") or "").strip()
    raw_packages = raw.get("packages")
    if (
        raw.get("schema") != REGISTRY_SCHEMA
        or not re.fullmatch(r"trusted-foundation-packages-v[1-9][0-9]*", policy_id)
        or argument_policy != ARGUMENT_POLICY
        or not isinstance(raw_packages, list)
        or not raw_packages
    ):
        raise ValueError("trusted-foundation registry policy header is invalid")

    packages: list[FoundationPackage] = []
    for index, raw_package in enumerate(raw_packages):
        if not isinstance(raw_package, dict) or set(raw_package) != {
            "module_root",
            "category",
            "semantic_policy",
        }:
            raise ValueError(
                f"trusted-foundation package {index} has an unexpected shape"
            )
        module_root = str(raw_package.get("module_root") or "").strip()
        category = str(raw_package.get("category") or "").strip()
        semantic_policy = str(raw_package.get("semantic_policy") or "").strip()
        if (
            not _MODULE_ROOT.fullmatch(module_root)
            or module_root in FORBIDDEN_WORKSPACE_ROOTS
            or category not in PACKAGE_CATEGORIES
            or semantic_policy != SEMANTIC_POLICY
        ):
            raise ValueError(f"trusted-foundation package {index} is invalid")
        packages.append(FoundationPackage(module_root, category, semantic_policy))

    roots = [package.module_root for package in packages]
    if roots != sorted(set(roots)):
        raise ValueError("trusted-foundation packages must be unique and root-sorted")
    package_tuple = tuple(packages)
    canonical = _canonical_payload(policy_id, argument_policy, package_tuple)
    digest = hashlib.sha256(
        json.dumps(canonical, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    return FoundationRegistry(
        policy_id=policy_id,
        argument_policy=argument_policy,
        packages=package_tuple,
        sha256=digest,
    )
