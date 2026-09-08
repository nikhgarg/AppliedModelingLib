#!/usr/bin/env python3
"""Declarative execution order for ordinary repository audit checks.

The strict paper-closeout executor remains a separate acceptance path.  This
module only owns the ordinary repository and reusable-library check registries;
the validators themselves remain on the repository audit service passed by the
caller.  Storing bound callables instead of method names keeps test patches and
direct-script imports on the same authoritative implementations.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from functools import partial
from pathlib import Path
from typing import Any, Callable, Generic, Iterable, TypeVar


FindingT = TypeVar("FindingT")

# These checks inspect spelling, comments, or source-level binder placement.
# They remain visible in ordinary CI; strict style additionally makes them
# blocking. Kernel closure, source/evidence validation, and proof placeholders
# are enforced by separate checks and never enter this set.
PRESENTATION_CHECKS = frozenset({
    "hidden_variable_premises",
    "library_source_assumption_standards",
    "library_reusable_provenance_language",
    "library_source_hygiene",
    "generic_source_reference_hygiene",
})


@dataclass(frozen=True)
class RegisteredCheck(Generic[FindingT]):
    """One named, already-bound audit check in deterministic execution order."""

    name: str
    run: Callable[[], list[FindingT]]


def _bound(
    name: str,
    function: Callable[..., list[FindingT]],
    /,
    *args: object,
    **kwargs: object,
) -> RegisteredCheck[FindingT]:
    """Bind one live validator without storing or resolving its name later."""

    return RegisteredCheck(name, partial(function, *args, **kwargs))


def execute_registered_checks(
    checks: Iterable[RegisteredCheck[FindingT]],
) -> list[FindingT]:
    """Run every registered check exactly once and preserve finding order."""

    findings: list[FindingT] = []
    seen: set[str] = set()
    for check in checks:
        if not check.name or check.name in seen:
            raise ValueError(
                "repository audit check name is empty or duplicated: "
                f"{check.name!r}"
            )
        seen.add(check.name)
        result = check.run()
        if not isinstance(result, list):
            raise TypeError(
                f"repository audit check `{check.name}` did not return a list"
            )
        findings.extend(result)
    return findings


def _presentation_policy(
    checks: Iterable[RegisteredCheck[Any]], *, strict_style: bool
) -> tuple[RegisteredCheck[Any], ...]:
    def advisory(check: RegisteredCheck[Any]) -> list[Any]:
        findings = check.run()
        if not isinstance(findings, list):
            raise TypeError(f"repository audit check `{check.name}` did not return a list")
        return [
            replace(finding, severity="WARN")
            if getattr(finding, "severity", None) == "ERROR" else finding
            for finding in findings
        ]

    return tuple(
        RegisteredCheck(check.name, partial(advisory, check))
        if not strict_style and check.name in PRESENTATION_CHECKS else check
        for check in checks
    )


def ordinary_repository_checks(
    audit: Any,
    *,
    include_active: bool,
    strict_style: bool,
    library_premise_audit: bool,
    paper_filter: str | None,
    require_source_bytes: bool,
    deep_paper_prose: bool,
) -> tuple[RegisteredCheck[Any], ...]:
    """Return the complete ordinary non-closeout repository check registry."""

    # This selection belongs to one ordered audit execution. The graph check
    # fills it only after invoking the canonical validator; errors stay in the
    # result and selected graphs never fall back to legacy evidence producers.
    graph_native_papers: set[str] = set()
    checks: list[RegisteredCheck[Any]] = [
        *(
            _bound(name, function, include_active)
            for name, function in (
                ("sorries", audit.check_sorries),
                ("axiom_like_declarations", audit.check_axiom_like_declarations),
                ("test_fixture_isolation", audit.check_test_fixture_isolation),
                ("hidden_variable_premises", audit.check_hidden_variable_premises),
                ("guarded_checks", audit.check_guarded_checks),
            )
        ),
        *(
            _bound(name, function)
            for name, function in (
                ("library_source_assumption_standards", audit.check_library_source_assumption_standards),
                ("library_reusable_provenance_language", audit.check_library_reusable_provenance_language),
                ("library_standard_definition_audits", audit.check_library_standard_definition_audits),
                ("library_source_hygiene", audit.check_library_source_hygiene),
                ("generic_source_reference_hygiene", audit.check_generic_source_reference_hygiene),
            )
        ),
        _bound("paper_contract", audit.check_paper_contract, include_active),
        _bound(
            "graph_native_paper_closure",
            audit.check_graph_native_paper_closure,
            include_active,
            paper_filter=paper_filter,
            require_source_bytes=require_source_bytes,
            selected_papers=graph_native_papers,
        ),
        _bound(
            "final_report_status_alignment",
            audit.check_final_report_status_alignment,
            include_active,
            paper_filter=paper_filter,
        ),
        _bound(
            "final_report_human_facing_front_matter",
            audit.check_final_report_human_facing_front_matter,
            include_active,
            paper_filter=paper_filter,
        ),
        _bound(
            "dag_and_validation_report_closeout",
            audit.check_dag_and_validation_report_closeout,
            include_active=include_active,
            paper_filter=paper_filter,
            public_graph_papers=graph_native_papers if not require_source_bytes else (),
        ),
        _bound("review_launcher_readiness", audit.check_review_launcher_readiness, include_active),
        _bound("dag_status_styles", audit.check_dag_status_styles),
        _bound("paper_facing_ledgers", audit.check_paper_facing_ledgers, include_active),
        _bound(
            "post_paper_audit_interfaces", audit.check_post_paper_audit_interfaces,
            include_active, graph_native_papers=graph_native_papers,
        ),
        _bound(
            "machine_paper_status",
            audit.check_machine_paper_status,
            library_premise_audit=library_premise_audit,
            paper_filter=paper_filter,
            paper_closeout=False,
            require_source_bytes=require_source_bytes,
            deep_paper_prose=deep_paper_prose,
            graph_native_papers=graph_native_papers,
        ),
        *(
            _bound(name, function)
            for name, function in (
                ("status_label_vocabulary", audit.check_status_label_vocabulary),
                ("generated_human_status_labels", audit.check_generated_human_status_labels),
            )
        ),
        _bound(
            "readme_status_tables",
            audit.check_readme_status_tables,
            include_active,
            paper_filter=paper_filter,
        ),
        _bound("tracked_artifacts", audit.check_tracked_artifacts, include_active),
        *(
            _bound(name, function)
            for name, function in (
                ("stale_architecture_terms", audit.check_stale_architecture_terms),
                ("root_readme_policy", audit.check_root_readme_policy),
                ("human_facing_readme", audit.check_human_facing_readme),
            )
        ),
    ]
    if strict_style:
        checks.append(_bound("strict_lean_style", audit.check_strict_lean_style))
    if library_premise_audit:
        checks.append(
            _bound(
                "library_certificate_boundaries",
                audit.check_library_certificate_boundaries,
            )
        )
    return _presentation_policy(checks, strict_style=strict_style)


def reusable_library_checks(
    audit: Any,
    *,
    files: Iterable[Path],
    strict_style: bool,
    library_premise_audit: bool,
) -> tuple[RegisteredCheck[Any], ...]:
    """Return the complete reusable-library-only check registry."""

    frozen_files = tuple(files)
    checks: list[RegisteredCheck[Any]] = [
        *(
            _bound(name, function, frozen_files)
            for name, function in (
                ("sorries", audit.check_sorries_in_files),
                ("axiom_like_declarations", audit.check_axiom_like_declarations_in_files),
                ("test_fixture_isolation", audit.check_test_fixture_isolation_in_files),
                ("hidden_variable_premises", audit.check_hidden_variable_premises_in_files),
                ("guarded_checks", audit.check_guarded_checks_in_files),
            )
        ),
        *(
            _bound(name, function)
            for name, function in (
                ("library_source_assumption_standards", audit.check_library_source_assumption_standards),
                ("library_reusable_provenance_language", audit.check_library_reusable_provenance_language),
                ("library_standard_definition_audits", audit.check_library_standard_definition_audits),
                ("library_source_hygiene", audit.check_library_source_hygiene),
            )
        ),
        _bound(
            "generic_source_reference_hygiene",
            audit.check_generic_source_reference_hygiene,
            library_only=True,
        ),
    ]
    if strict_style:
        checks.append(_bound("strict_lean_style", audit.check_strict_lean_style))
    if library_premise_audit:
        checks.append(
            _bound(
                "library_certificate_boundaries",
                audit.check_library_certificate_boundaries,
            )
        )
    return _presentation_policy(checks, strict_style=strict_style)
