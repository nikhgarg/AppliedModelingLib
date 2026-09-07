#!/usr/bin/env python3
"""Plan, install, or enumerate paper targets in ``lakefile.toml``.

The registrar intentionally performs one narrow append-only edit. It does not
change ``defaultTargets`` or rewrite TOML formatting, so adding a paper target
does not perturb unrelated paper routing or closeout identities.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import re
import stat
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Mapping, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:
    from scripts.tomllib_compat import tomllib
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from tomllib_compat import tomllib

try:
    from scripts.lean_process_diagnostics import (
        bounded_lean_diagnostic_excerpt,
        lean_diagnostic_failure_reason,
    )
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from lean_process_diagnostics import (
        bounded_lean_diagnostic_excerpt,
        lean_diagnostic_failure_reason,
    )

DEFAULT_LAKEFILE = ROOT / "lakefile.toml"
PAPER_ID_RE = re.compile(r"^[A-Z][A-Za-z0-9]*\d{2}[A-Z][A-Za-z0-9]*$")
CANONICAL_SRC_DIR = "papers"


class PaperTargetRegistrationError(ValueError):
    """Raised when a paper target cannot be added without changing Lake semantics."""


@dataclass(frozen=True)
class PaperTargetRegistrationPlan:
    """A byte-exact registration plan already verified through TOML reparsing."""

    paper_id: str
    lakefile: Path
    original_sha256: str
    rendered_sha256: str
    original_bytes: bytes = field(repr=False)
    rendered_bytes: bytes = field(repr=False)
    original_payload: Mapping[str, Any] = field(repr=False)
    rendered_payload: Mapping[str, Any] = field(repr=False)

    @property
    def registration(self) -> dict[str, str]:
        return {"name": self.paper_id, "srcDir": CANONICAL_SRC_DIR}

    def summary(self, *, written: bool = False) -> dict[str, object]:
        return {
            "schema": 1,
            "paper": self.paper_id,
            "lakefile": str(self.lakefile),
            "action": "registered" if written else "append_registration",
            "written": written,
            "registration": self.registration,
            "default_targets_changed": False,
            "original_sha256": self.original_sha256,
            "rendered_sha256": self.rendered_sha256,
        }


def validate_paper_id(paper_id: str) -> str:
    """Return one canonical citation-style paper identifier or fail closed."""

    if not isinstance(paper_id, str) or not PAPER_ID_RE.fullmatch(paper_id):
        raise PaperTargetRegistrationError(
            "paper id must match [AuthorInitials][2DigitYear][Descriptor]"
        )
    return paper_id


def _parse_lakefile(content: bytes, *, label: str) -> dict[str, Any]:
    try:
        text = content.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise PaperTargetRegistrationError(f"{label} is not UTF-8: {exc}") from exc
    try:
        payload = tomllib.loads(text)
    except tomllib.TOMLDecodeError as exc:
        raise PaperTargetRegistrationError(f"{label} is not valid TOML: {exc}") from exc
    if not isinstance(payload, dict):  # Defensive: tomllib currently always returns dict.
        raise PaperTargetRegistrationError(f"{label} did not parse as a TOML table")
    return payload


def _validated_libraries(payload: Mapping[str, Any]) -> list[dict[str, Any]]:
    raw_libraries = payload.get("lean_lib", [])
    if not isinstance(raw_libraries, list):
        raise PaperTargetRegistrationError("lakefile.toml lean_lib must be an array of tables")

    libraries: list[dict[str, Any]] = []
    names: set[str] = set()
    casefolded_names: dict[str, str] = {}
    for index, raw_library in enumerate(raw_libraries):
        if not isinstance(raw_library, dict):
            raise PaperTargetRegistrationError(
                f"lakefile.toml lean_lib entry {index} is not a table"
            )
        name = raw_library.get("name")
        if not isinstance(name, str) or not name.strip() or name != name.strip():
            raise PaperTargetRegistrationError(
                f"lakefile.toml lean_lib entry {index} has no canonical string name"
            )
        if name in names:
            raise PaperTargetRegistrationError(
                f"lakefile.toml has duplicate lean_lib target `{name}`"
            )
        folded = name.casefold()
        prior = casefolded_names.get(folded)
        if prior is not None:
            raise PaperTargetRegistrationError(
                "lakefile.toml has case-conflicting lean_lib targets "
                f"`{prior}` and `{name}`"
            )
        names.add(name)
        casefolded_names[folded] = name
        libraries.append(copy.deepcopy(raw_library))
    return libraries


def registered_target_names(lakefile: Path | str) -> tuple[str, ...]:
    """Return every configured Lean library target in declaration order.

    Integration builds use this instead of ``defaultTargets``. New paper
    registration deliberately leaves the default list unchanged so a focused
    paper PR cannot perturb unrelated build-control identities.
    """

    path = Path(lakefile)
    try:
        content = path.read_bytes()
    except OSError as exc:
        raise PaperTargetRegistrationError(f"could not read {path}: {exc}") from exc
    payload = _parse_lakefile(content, label=str(path))
    return tuple(str(library["name"]) for library in _validated_libraries(payload))


def build_registered_targets(lakefile: Path | str) -> int:
    """Build every registered Lean library with bounded, fail-closed output.

    This is the occasional integration backstop for shared-library or routing
    changes.  It is deliberately broader than ``defaultTargets`` but is not a
    paper-closeout or routine engine-revision gate.  Capture the complete Lean
    stream so a zero-exit panic, internal error, crash backtrace, or pathological
    diagnostic volume cannot be hidden by Lake's return code, while operators
    see only a bounded failure excerpt.
    """

    targets = registered_target_names(lakefile)
    if not targets:
        raise PaperTargetRegistrationError("lakefile.toml registers no Lean libraries")
    command = ["lake", "-q", "build", *targets]
    print("+ " + " ".join(command), flush=True)
    result = subprocess.run(
        command,
        cwd=Path(lakefile).resolve().parent,
        capture_output=True,
        text=True,
        check=False,
    )
    stdout = str(result.stdout or "")
    stderr = str(result.stderr or "")
    diagnostic = lean_diagnostic_failure_reason(stdout, stderr)
    if result.returncode != 0 or diagnostic:
        reason = diagnostic or f"Lake exited with code {result.returncode}"
        print(f"registered-target integration build failed: {reason}", file=sys.stderr)
        excerpt = bounded_lean_diagnostic_excerpt(
            stdout,
            stderr,
            max_lines=12,
            max_chars=2000,
        )
        if excerpt:
            print(excerpt, file=sys.stderr)
        return result.returncode or 1
    print(f"OK built {len(targets)} registered Lean libraries")
    return 0


def _registration_block(paper_id: str) -> bytes:
    return (
        "[[lean_lib]]\n"
        f'name = "{paper_id}"\n'
        f'srcDir = "{CANONICAL_SRC_DIR}"\n'
    ).encode("ascii")


def _append_registration(original: bytes, paper_id: str) -> bytes:
    if original.endswith(b"\n\n"):
        separator = b""
    elif original.endswith(b"\n"):
        separator = b"\n"
    else:
        separator = b"\n\n"
    return original + separator + _registration_block(paper_id)


def _expected_payload(
    original_payload: Mapping[str, Any], paper_id: str
) -> dict[str, Any]:
    expected = copy.deepcopy(dict(original_payload))
    raw_libraries = expected.get("lean_lib")
    libraries = [] if raw_libraries is None else list(raw_libraries)
    libraries.append({"name": paper_id, "srcDir": CANONICAL_SRC_DIR})
    expected["lean_lib"] = libraries
    return expected


def registration_is_exact_addition(
    original_text: str,
    candidate_text: str,
    paper_id: str,
) -> bool:
    """Return whether candidate is the canonical one-target append to original.

    This is the base/head verifier used by contributor scope classification.
    It checks bytes as well as parsed TOML semantics, so a broader rewrite
    cannot hide behind an equivalent parser result.
    """

    paper_id = validate_paper_id(paper_id)
    original = original_text.encode("utf-8")
    candidate = candidate_text.encode("utf-8")
    original_payload = _parse_lakefile(original, label="base lakefile.toml")
    libraries = _validated_libraries(original_payload)
    if any(
        str(library["name"]).casefold() == paper_id.casefold()
        for library in libraries
    ):
        raise PaperTargetRegistrationError(
            f"paper target `{paper_id}` already exists in the base Lake configuration"
        )
    expected_bytes = _append_registration(original, paper_id)
    if candidate != expected_bytes:
        return False
    candidate_payload = _parse_lakefile(candidate, label="candidate lakefile.toml")
    _validated_libraries(candidate_payload)
    return candidate_payload == _expected_payload(original_payload, paper_id)


def plan_paper_target_registration(
    lakefile: Path | str, paper_id: str
) -> PaperTargetRegistrationPlan:
    """Return a verified append-only plan without writing the Lake file."""

    paper_id = validate_paper_id(paper_id)
    path = Path(lakefile)
    if path.is_symlink():
        raise PaperTargetRegistrationError("refusing to replace a symlinked lakefile.toml")
    if not path.is_file():
        raise PaperTargetRegistrationError(f"Lake configuration is not a file: {path}")

    try:
        original = path.read_bytes()
    except OSError as exc:
        raise PaperTargetRegistrationError(f"could not read {path}: {exc}") from exc
    original_payload = _parse_lakefile(original, label=str(path))
    libraries = _validated_libraries(original_payload)
    for library in libraries:
        name = str(library["name"])
        if name == paper_id:
            if library == {"name": paper_id, "srcDir": CANONICAL_SRC_DIR}:
                raise PaperTargetRegistrationError(
                    f"paper target `{paper_id}` is already registered"
                )
            raise PaperTargetRegistrationError(
                f"paper target `{paper_id}` conflicts with an existing lean_lib entry"
            )
        if name.casefold() == paper_id.casefold():
            raise PaperTargetRegistrationError(
                f"paper target `{paper_id}` case-conflicts with existing target `{name}`"
            )

    rendered = _append_registration(original, paper_id)
    if not rendered.startswith(original) or rendered == original:
        raise PaperTargetRegistrationError("registration rendering is not append-only")
    rendered_payload = _parse_lakefile(rendered, label="rendered lakefile.toml")
    _validated_libraries(rendered_payload)
    expected_payload = _expected_payload(original_payload, paper_id)
    if rendered_payload != expected_payload:
        raise PaperTargetRegistrationError(
            "rendered Lake configuration changes content other than one appended lean_lib"
        )

    return PaperTargetRegistrationPlan(
        paper_id=paper_id,
        lakefile=path,
        original_sha256=hashlib.sha256(original).hexdigest(),
        rendered_sha256=hashlib.sha256(rendered).hexdigest(),
        original_bytes=original,
        rendered_bytes=rendered,
        original_payload=original_payload,
        rendered_payload=rendered_payload,
    )


def _atomic_install(plan: PaperTargetRegistrationPlan) -> None:
    path = plan.lakefile
    try:
        original_stat = path.stat()
    except OSError as exc:
        raise PaperTargetRegistrationError(f"could not stat {path}: {exc}") from exc

    descriptor, temporary_name = tempfile.mkstemp(
        dir=path.parent,
        prefix=f".{path.name}.registration-",
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            os.fchmod(stream.fileno(), stat.S_IMODE(original_stat.st_mode))
            stream.write(plan.rendered_bytes)
            stream.flush()
            os.fsync(stream.fileno())

        try:
            current = path.read_bytes()
        except OSError as exc:
            raise PaperTargetRegistrationError(
                f"could not recheck {path} before replacement: {exc}"
            ) from exc
        if current != plan.original_bytes:
            raise PaperTargetRegistrationError(
                "lakefile.toml changed after registration planning; replan before writing"
            )
        os.replace(temporary, path)

        try:
            directory_fd = os.open(path.parent, os.O_RDONLY)
        except OSError:
            directory_fd = -1
        if directory_fd >= 0:
            try:
                os.fsync(directory_fd)
            finally:
                os.close(directory_fd)
    except BaseException:
        try:
            temporary.unlink(missing_ok=True)
        except OSError:
            pass
        raise


def register_paper_target(
    lakefile: Path | str, paper_id: str
) -> PaperTargetRegistrationPlan:
    """Atomically install and verify one paper target registration."""

    plan = plan_paper_target_registration(lakefile, paper_id)
    _atomic_install(plan)
    try:
        installed = plan.lakefile.read_bytes()
    except OSError as exc:
        raise PaperTargetRegistrationError(
            f"could not verify installed {plan.lakefile}: {exc}"
        ) from exc
    if installed != plan.rendered_bytes:
        raise PaperTargetRegistrationError(
            "installed lakefile.toml does not match the verified registration plan"
        )
    installed_payload = _parse_lakefile(installed, label=str(plan.lakefile))
    if installed_payload != plan.rendered_payload:
        raise PaperTargetRegistrationError(
            "installed Lake configuration failed semantic registration verification"
        )
    return plan


def restore_paper_target_registration(plan: PaperTargetRegistrationPlan) -> None:
    """Restore a failed scaffold's exact pre-registration Lake bytes.

    The rollback is compare-and-swap: it never overwrites a concurrent edit.
    Calling it before the registration was installed is a harmless no-op.
    """

    try:
        current = plan.lakefile.read_bytes()
    except OSError as exc:
        raise PaperTargetRegistrationError(
            f"could not inspect {plan.lakefile} for rollback: {exc}"
        ) from exc
    if current == plan.original_bytes:
        return
    if current != plan.rendered_bytes:
        raise PaperTargetRegistrationError(
            "lakefile.toml changed after paper registration; refusing rollback"
        )
    reverse = PaperTargetRegistrationPlan(
        paper_id=plan.paper_id,
        lakefile=plan.lakefile,
        original_sha256=plan.rendered_sha256,
        rendered_sha256=plan.original_sha256,
        original_bytes=plan.rendered_bytes,
        rendered_bytes=plan.original_bytes,
        original_payload=plan.rendered_payload,
        rendered_payload=plan.original_payload,
    )
    _atomic_install(reverse)
    if plan.lakefile.read_bytes() != plan.original_bytes:
        raise PaperTargetRegistrationError(
            "paper target registration rollback did not restore exact bytes"
        )


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    for command, help_text in (
        ("plan", "validate and print the append-only registration plan"),
        ("register", "atomically append and verify the paper target"),
    ):
        child = subparsers.add_parser(command, help=help_text)
        child.add_argument("paper", help="citation-style paper folder/target name")
        child.add_argument(
            "--lakefile",
            type=Path,
            default=DEFAULT_LAKEFILE,
            help=f"Lake TOML file (default: {DEFAULT_LAKEFILE})",
        )
    build = subparsers.add_parser(
        "build-all",
        help="build every registered Lean library, including non-default papers",
    )
    build.add_argument(
        "--lakefile",
        type=Path,
        default=DEFAULT_LAKEFILE,
        help=f"Lake TOML file (default: {DEFAULT_LAKEFILE})",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        if args.command == "build-all":
            return build_registered_targets(args.lakefile)
        if args.command == "register":
            plan = register_paper_target(args.lakefile, args.paper)
            written = True
        else:
            plan = plan_paper_target_registration(args.lakefile, args.paper)
            written = False
    except (OSError, PaperTargetRegistrationError) as exc:
        print(f"paper target registration failed: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(plan.summary(written=written), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
