#!/usr/bin/env python3
"""Create the standard AppliedModelingLib paper-formalization scaffold.

The script performs the deterministic intake step for a new source paper:
create the citation-specific folder, cache the source PDF when possible,
extract a text cache with `pdftotext` when available, and write the required
source map, semantic/proof interfaces, status, working memo, and plan. Final
validation reports and dependency DAGs are planner-owned closeout artifacts,
not intake placeholders.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
import urllib.parse
import urllib.request
from dataclasses import dataclass
from datetime import date
from pathlib import Path

from scripts.formalization_protocol import resolve_closeout_review_policy

ROOT = Path(__file__).resolve().parents[1]
PAPERS = ROOT / "papers"
FOLDER_RE = re.compile(r"^[A-Z][A-Za-z0-9]*\d{2}[A-Z][A-Za-z0-9]*$")
LEAN_NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
LEAN_NAMESPACE_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$"
)
PLACEHOLDER_RE = re.compile(
    r"(?:\bTODO\b|\bTBD\b|\bplaceholder\b|\bto be (?:filled|refined|replaced)\b|"
    r"\[paper|\[source|<paper|<source)",
    re.IGNORECASE,
)
SOURCE_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
EXACT_SOURCE_LOCATOR_RE = re.compile(
    r"(?:"
    r"\b(?:page|p\.?)\s*\d+|"
    r"\bappendix\s+[A-Z0-9]+|"
    r"\b(?:section|theorem|lemma|proposition|corollary|definition|equation|"
    r"remark|claim|line)s?\s+(?:[A-Z]?\d[\w.()/-]*|[A-Z](?:\.\d+)*)|"
    r"§\s*[A-Z0-9]+|"
    r"\b[\w./-]+\.(?:tex|txt|md|pdf):\d+"
    r")",
    re.IGNORECASE,
)
SOURCE_KINDS = {
    "lemma",
    "theorem",
    "proposition",
    "corollary",
    "claim",
    "runtime_claim",
}
LEAN_BREAKOUT_LINE_RE = re.compile(
    r"(?m)^\s*(?:#|@\[|import\b|namespace\b|section\b|end\b|open\b|export\b|"
    r"universe\b|variable\b|include\b|omit\b|attribute\b|set_option\b|"
    r"private\b|protected\b|noncomputable\b|theorem\b|lemma\b|def\b|abbrev\b|"
    r"axiom\b|opaque\b|constant\b|structure\b|class\b|inductive\b|instance\b|"
    r"example\b|where\b|deriving\b)",
)
LEAN_RENDERED_DECL_RE = re.compile(
    r"(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*"
    r"(theorem|lemma|def|abbrev|axiom|opaque|constant|structure|class|inductive|"
    r"instance|example)\s+([A-Za-z_][A-Za-z0-9_']*)\b"
)
SCAFFOLD_META_SENTINEL = "ECONCS_SCAFFOLD_TARGET_OK:"
SEMANTIC_MODEL_DIMENSION_ORDER = (
    "expanded_binders_and_domain",
    "carrier_and_domain",
    "probability_support_endpoints",
    "joint_law_and_state_evolution",
    "conditioning_and_calibration_semantics",
    "expectation_definedness",
    "null_cell_totalization_and_partition_scope",
    "extended_rate_codomain",
)
SEMANTIC_MODEL_REVIEW_SCHEMA = 2


@dataclass(frozen=True)
class StatementTarget:
    """One source-pinned proposition transcription to seed as an honest proof hole."""

    source_item: str
    source_location: str
    source_statement: str
    lean_name: str
    lean_type: str
    source_kind: str
    kind: str = "theorem"


@dataclass(frozen=True)
class StatementSpec:
    """Pinned source artifact plus exact source-to-Lean target routing."""

    targets: list[StatementTarget]
    source_artifact_path: Path
    source_artifact_sha256: str
    source_version: str


def statement_spec_name(target: StatementTarget) -> str:
    """Return the transparent proposition name paired with one proof target."""

    return f"{target.lean_name}Spec"


def statement_first_review_names(targets: list[StatementTarget]) -> list[str]:
    """Return one expanded semantic target per source claim, in source order."""

    return [statement_spec_name(target) for target in targets]


def statement_first_spec_proof_routes(targets: list[StatementTarget]) -> dict[str, str]:
    """Return the exact Prop-spec to theorem/lemma routes for later Meta checks."""

    return {statement_spec_name(target): target.lean_name for target in targets}


def statement_first_semantic_contract_template(
    target: StatementTarget,
) -> dict[str, str]:
    """Return an inactive exact-contract route for one audited source target.

    This is deliberately *not* named ``semantic_contract``.  The source text
    still needs an independent source-atom inventory, and the theorem body is
    still a proof hole. At closeout the route must also satisfy the v11
    source-to-Spec correspondence and full Lean-closure audit; these four
    routing fields never supply that evidence themselves.
    """

    return {
        "spec_declaration": statement_spec_name(target),
        "evidence_declaration": target.lean_name,
        "evidence_mode": "proves",
        "semantic_shape": "plain",
    }


def _required_target_text(raw: object, field: str, index: int) -> str:
    value = raw.strip() if isinstance(raw, str) else ""
    if not value:
        raise ValueError(f"statement target {index} has no `{field}`")
    if PLACEHOLDER_RE.search(value):
        raise ValueError(
            f"statement target {index} `{field}` is still placeholder text"
        )
    return value


def load_statement_spec(path: Path) -> StatementSpec:
    """Load targets only after verifying their pinned source artifact bytes."""

    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except OSError as exc:
        raise ValueError(
            f"could not read statement target spec `{path}`: {exc}"
        ) from exc
    except json.JSONDecodeError as exc:
        raise ValueError(
            f"invalid JSON in statement target spec `{path}`: {exc}"
        ) from exc
    if not isinstance(payload, dict) or payload.get("schema") != 1:
        raise ValueError("statement target spec must be an object with `schema: 1`")
    source_artifact_raw = _required_target_text(
        payload.get("source_artifact_path"), "source_artifact_path", 0
    )
    source_artifact_path = Path(source_artifact_raw).expanduser()
    if not source_artifact_path.is_absolute():
        source_artifact_path = (path.parent / source_artifact_path).resolve()
    if not source_artifact_path.is_file():
        raise ValueError(
            f"statement target spec source artifact does not exist: `{source_artifact_path}`"
        )
    recorded_source_sha256 = (
        str(payload.get("source_artifact_sha256") or "").strip().lower()
    )
    if not SOURCE_SHA256_RE.fullmatch(recorded_source_sha256):
        raise ValueError(
            "statement target spec needs a 64-hex `source_artifact_sha256`"
        )
    actual_source_sha256 = hashlib.sha256(source_artifact_path.read_bytes()).hexdigest()
    if recorded_source_sha256 != actual_source_sha256:
        raise ValueError(
            "statement target spec source_artifact_sha256 does not match source artifact bytes"
        )
    source_version = _required_target_text(
        payload.get("source_version"), "source_version", 0
    )
    raw_targets = payload.get("targets")
    if not isinstance(raw_targets, list) or not raw_targets:
        raise ValueError("statement target spec must contain a nonempty `targets` list")

    targets: list[StatementTarget] = []
    seen_names: set[str] = set()
    for index, raw in enumerate(raw_targets, start=1):
        if not isinstance(raw, dict):
            raise ValueError(f"statement target {index} is not an object")
        kind = str(raw.get("kind") or "theorem").strip()
        if kind not in {"theorem", "lemma"}:
            raise ValueError(
                f"statement target {index} has unsupported kind `{kind}`; use theorem or lemma"
            )
        lean_name = _required_target_text(raw.get("lean_name"), "lean_name", index)
        if not LEAN_NAME_RE.fullmatch(lean_name):
            raise ValueError(
                f"statement target {index} has unsafe Lean name `{lean_name}`; "
                "use an unqualified identifier"
            )
        if lean_name in seen_names:
            raise ValueError(f"duplicate statement target Lean name `{lean_name}`")
        seen_names.add(lean_name)
        lean_type = _required_target_text(raw.get("lean_type"), "lean_type", index)
        if lean_type in {"True", "Prop"}:
            raise ValueError(
                f"statement target {index} uses the bare placeholder type `{lean_type}`"
            )
        _validate_lean_type_fragment(lean_type, index)
        source_statement = _required_target_text(
            raw.get("source_statement"), "source_statement", index
        )
        if "/-" in source_statement or "-/" in source_statement:
            raise ValueError(
                f"statement target {index} source statement contains a Lean comment delimiter"
            )
        source_item = _required_target_text(
            raw.get("source_item"), "source_item", index
        )
        source_location = _required_target_text(
            raw.get("source_location"), "source_location", index
        )
        if any(
            token in value
            for value in (source_item, source_location)
            for token in ("/-", "-/")
        ):
            raise ValueError(
                f"statement target {index} source metadata contains a Lean comment delimiter"
            )
        if not EXACT_SOURCE_LOCATOR_RE.search(source_location):
            raise ValueError(f"statement target {index} has no exact source locator")
        source_kind = _required_target_text(
            raw.get("source_kind"), "source_kind", index
        ).lower()
        if source_kind not in SOURCE_KINDS:
            raise ValueError(
                f"statement target {index} has unsupported source_kind `{source_kind}`"
            )
        targets.append(
            StatementTarget(
                source_item=source_item,
                source_location=source_location,
                source_statement=source_statement,
                lean_name=lean_name,
                lean_type=lean_type,
                source_kind=source_kind,
                kind=kind,
            )
        )
    generated_names: dict[str, str] = {}
    for target in targets:
        for declaration_name, role in (
            (statement_spec_name(target), "generated proposition specification"),
            (target.lean_name, "proof declaration"),
        ):
            previous = generated_names.get(declaration_name)
            if previous is not None:
                raise ValueError(
                    "statement target names collide after generating `...Spec`: "
                    f"`{declaration_name}` would be both {previous} and {role}"
                )
            generated_names[declaration_name] = role

    return StatementSpec(
        targets=targets,
        source_artifact_path=source_artifact_path,
        source_artifact_sha256=actual_source_sha256,
        source_version=source_version,
    )


def load_statement_targets(path: Path) -> list[StatementTarget]:
    """Compatibility wrapper for callers that only need target declarations."""

    return load_statement_spec(path).targets


def title_case_slug(text: str) -> str:
    parts = [part for part in re.split(r"[^A-Za-z0-9]+", text) if part]
    if not parts:
        return "Paper"
    return "".join(part[:1].upper() + part[1:] for part in parts)


def derive_folder(url: str) -> str:
    parsed = urllib.parse.urlparse(url)
    stem = Path(parsed.path).stem or parsed.netloc or "paper"
    stem = re.sub(r"^abs$", "", stem)
    slug = title_case_slug(stem)
    return f"Draft{date.today().year % 100:02d}{slug}"


def lean_namespace(folder: str) -> str:
    namespace = re.sub(r"[^A-Za-z0-9_]", "", folder)
    if not namespace or namespace[0].isdigit():
        namespace = f"Paper{namespace}"
    return namespace


def validate_scaffold_cli_inputs(
    args: argparse.Namespace, folder: str, namespace: str
) -> None:
    """Reject path and Lean-source injection through scaffold CLI metadata."""

    if Path(folder).name != folder or not FOLDER_RE.fullmatch(folder):
        raise ValueError(
            "--folder must be one safe path component matching "
            "[AuthorInitials][2DigitYear][Descriptor]"
        )
    if not LEAN_NAMESPACE_RE.fullmatch(namespace):
        raise ValueError("--namespace must be a qualified Lean identifier")
    title = str(args.title or "")
    if any(token in title for token in ("\n", "\r", "/-", "-/")):
        raise ValueError(
            "--title must be one line and may not contain Lean comment delimiters"
        )


def normalize_pdf_url(url: str) -> str:
    parsed = urllib.parse.urlparse(url)
    if parsed.netloc.endswith("arxiv.org"):
        if parsed.path.startswith("/abs/"):
            arxiv_id = parsed.path.removeprefix("/abs/")
            return urllib.parse.urlunparse(
                parsed._replace(path=f"/pdf/{arxiv_id}.pdf", query="")
            )
        if parsed.path.startswith("/pdf/") and not parsed.path.endswith(".pdf"):
            return urllib.parse.urlunparse(
                parsed._replace(path=f"{parsed.path}.pdf", query="")
            )
    return url


def audited_source_filename(source: Path) -> str:
    """Return a stable paper-local name while preserving the artifact format."""

    suffixes = "".join(source.suffixes).lower()
    if not suffixes or not re.fullmatch(r"(?:\.[a-z0-9]+)+", suffixes):
        suffixes = ".bin"
    return f"source-audited{suffixes}"


def _validate_lean_type_fragment(value: str, index: int) -> None:
    """Reject syntax that can escape the generated theorem's type position."""

    if any(token in value for token in ("--", "/-", "-/")):
        raise ValueError(
            f"statement target {index} Lean type may not contain Lean comments"
        )
    if LEAN_BREAKOUT_LINE_RE.search(value):
        raise ValueError(
            f"statement target {index} Lean type contains a top-level command or declaration"
        )

    stack: list[str] = []
    matching = {")": "(", "]": "[", "}": "{"}
    in_string = False
    escaped = False
    line_start = 0
    cursor = 0
    while cursor < len(value):
        char = value[cursor]
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            cursor += 1
            continue
        if char == '"':
            in_string = True
            cursor += 1
            continue
        if char in "([{":
            stack.append(char)
        elif char in ")]}":
            if not stack or stack.pop() != matching[char]:
                raise ValueError(
                    f"statement target {index} Lean type has unbalanced delimiters"
                )
        elif char == "\n":
            line_start = cursor + 1
        elif value.startswith(":=", cursor) and not stack:
            line_prefix = value[line_start:cursor].strip()
            if not re.match(r"^let(?:\s+rec)?\b", line_prefix):
                raise ValueError(
                    f"statement target {index} Lean type contains a top-level `:=` breakout"
                )
            cursor += 1
        cursor += 1
    if in_string or stack:
        raise ValueError(
            f"statement target {index} Lean type has an unterminated literal or delimiter"
        )


def _mask_lean_comments_and_strings(source: str) -> str:
    """Mask non-code while preserving offsets/newlines for scaffold assertions."""

    out = list(source)
    cursor = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    escaped = False
    while cursor < len(source):
        if in_line_comment:
            if source[cursor] == "\n":
                in_line_comment = False
            else:
                out[cursor] = " "
            cursor += 1
            continue
        if block_depth:
            if source.startswith("/-", cursor):
                out[cursor] = out[cursor + 1] = " "
                block_depth += 1
                cursor += 2
                continue
            if source.startswith("-/", cursor):
                out[cursor] = out[cursor + 1] = " "
                block_depth -= 1
                cursor += 2
                continue
            if source[cursor] != "\n":
                out[cursor] = " "
            cursor += 1
            continue
        if in_string:
            if source[cursor] != "\n":
                out[cursor] = " "
            if escaped:
                escaped = False
            elif source[cursor] == "\\":
                escaped = True
            elif source[cursor] == '"':
                in_string = False
            cursor += 1
            continue
        if source.startswith("--", cursor):
            out[cursor] = out[cursor + 1] = " "
            in_line_comment = True
            cursor += 2
            continue
        if source.startswith("/-", cursor):
            out[cursor] = out[cursor + 1] = " "
            block_depth = 1
            cursor += 2
            continue
        if source[cursor] == '"':
            out[cursor] = " "
            in_string = True
        cursor += 1
    if block_depth or in_string:
        raise ValueError(
            "rendered statement interface has an unterminated comment or string"
        )
    return "".join(out)


def validate_rendered_statement_interface(
    namespace: str,
    targets: list[StatementTarget],
    rendered: str,
    timeout_seconds: int = 120,
) -> None:
    """Statically partition, then Lean-check the human semantic surface."""

    masked = _mask_lean_comments_and_strings(rendered)
    declarations = list(LEAN_RENDERED_DECL_RE.finditer(masked))
    actual = [(match.group(1), match.group(2)) for match in declarations]
    expected = [("def", statement_spec_name(target)) for target in targets]
    if actual != expected:
        raise ValueError(
            "rendered statement interface contains declarations outside the requested targets"
        )
    end_marker = f"\n\nend {namespace}"
    namespace_end = masked.rfind(end_marker)
    if namespace_end < 0:
        raise ValueError(
            "rendered statement interface has no expected namespace terminator"
        )

    def normalized_code(text: str) -> str:
        return re.sub(r"\s+", " ", text).strip()

    for target_index, target in enumerate(targets):
        spec_declaration = declarations[target_index]
        spec_end = (
            declarations[target_index + 1].start()
            if target_index + 1 < len(declarations)
            else namespace_end
        )
        spec_block = masked[spec_declaration.start() : spec_end].strip()
        expected_spec = (
            f"def {statement_spec_name(target)} : Prop := {target.lean_type}"
        )
        if normalized_code(spec_block) != normalized_code(expected_spec):
            raise ValueError(
                f"rendered target `{target.lean_name}` does not have the exact generated "
                "transparent `...Spec : Prop` declaration"
            )

    start_marker = f"namespace {namespace}\n\n"
    payload_start = rendered.find(start_marker)
    payload_end = rendered.rfind(end_marker)
    if payload_start < 0 or payload_end < 0:
        raise ValueError("could not isolate rendered statement declarations")
    declarations_source = rendered[payload_start + len(start_marker) : payload_end]
    meta_helper = r"""
open Lean Meta Elab Command
    syntax "#assert_scaffold_spec " str : command
    elab_rules : command
  | `(#assert_scaffold_spec $spec:str) => do
      let specName := spec.getString.toName
      let specInfo ← liftTermElabM (getConstInfo specName)
      match specInfo with
      | .defnInfo definitionInfo =>
          let isProposition ← liftTermElabM (isProp definitionInfo.value)
          unless isProposition do
            throwError "scaffold specification is not Prop-valued"
          if definitionInfo.value.hasSorry then
            throwError "scaffold specification contains sorryAx"
      | _ =>
          throwError "scaffold specification is not a transparent definition"
      IO.println s!"ECONCS_SCAFFOLD_TARGET_OK:{specName}"
"""
    commands = "\n".join(
        "#assert_scaffold_spec "
        f"{json.dumps(f'{namespace}.{statement_spec_name(target)}')}"
        for target in targets
    )
    validation_import = "import AppliedModelingLib\n\n" if targets else "import Lean\n\n"
    validation_source = (
        validation_import
        + f"namespace {namespace}\n\n{declarations_source}\n\nend {namespace}\n\n"
        f"{meta_helper}\n{commands}\n"
    )
    project_root = Path(__file__).resolve().parents[1]
    with tempfile.TemporaryDirectory() as temp_dir:
        validation_path = Path(temp_dir) / "statement_scaffold_validation.lean"
        validation_path.write_text(validation_source, encoding="utf-8")
        try:
            proc = subprocess.run(
                ["lake", "env", "lean", str(validation_path)],
                cwd=project_root,
                check=False,
                capture_output=True,
                text=True,
                timeout=timeout_seconds,
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise ValueError(
                f"Lean could not validate rendered statement targets: {exc}"
            ) from exc
    if proc.returncode != 0:
        details = (proc.stdout or proc.stderr).strip().splitlines()
        excerpt = " ".join(details[:4])[:800]
        raise ValueError(
            "Lean rejected the rendered statement targets"
            + (f": {excerpt}" if excerpt else "")
        )
    reported = {
        line.split(SCAFFOLD_META_SENTINEL, 1)[1].strip()
        for line in proc.stdout.splitlines()
        if SCAFFOLD_META_SENTINEL in line
    }
    expected_names = {f"{namespace}.{statement_spec_name(target)}" for target in targets}
    if reported != expected_names:
        raise ValueError(
            "Lean did not validate exactly the requested statement targets"
        )


def validate_rendered_proof_interface(
    namespace: str,
    targets: list[StatementTarget],
    rendered: str,
) -> None:
    """Require one exact-type draft proof endpoint outside the human interface."""

    masked = _mask_lean_comments_and_strings(rendered)
    declarations = list(LEAN_RENDERED_DECL_RE.finditer(masked))
    actual = [(match.group(1), match.group(2)) for match in declarations]
    expected = [(target.kind, target.lean_name) for target in targets]
    if actual != expected:
        raise ValueError(
            "rendered proof interface contains declarations outside the requested targets"
        )
    end_marker = f"\n\nend {namespace}"
    namespace_end = masked.rfind(end_marker)
    if namespace_end < 0:
        raise ValueError("rendered proof interface has no expected namespace terminator")

    def normalized_code(text: str) -> str:
        return re.sub(r"\s+", " ", text).strip()

    for index, target in enumerate(targets):
        declaration = declarations[index]
        declaration_end = (
            declarations[index + 1].start()
            if index + 1 < len(declarations)
            else namespace_end
        )
        block = masked[declaration.start() : declaration_end].strip()
        expected_block = (
            f"{target.kind} {target.lean_name} : "
            f"{statement_spec_name(target)} := by sorry"
        )
        if normalized_code(block) != normalized_code(expected_block):
            raise ValueError(
                f"rendered proof endpoint `{target.lean_name}` does not have the generated "
                "`...Spec := by sorry` proof body"
            )


def write_file(path: Path, contents: str, force: bool) -> None:
    if path.exists() and not force:
        print(f"skip existing {path.relative_to(ROOT)}")
        return
    path.write_text(contents, encoding="utf-8")
    print(f"wrote {path.relative_to(ROOT)}")


def refresh_review_cache(folder: str) -> None:
    """Run the review metadata bootstrap for a fresh paper scaffold."""

    cmd = [
        "python3",
        str(ROOT / "scripts" / "review_dashboard.py"),
        "--paper",
        folder,
        "--refresh-cache",
    ]
    try:
        proc = subprocess.run(
            cmd, cwd=str(ROOT), check=False, capture_output=True, text=True
        )
    except OSError as exc:
        print(f"warning: could not refresh review cache for {folder}: {exc}")
        return
    if proc.returncode != 0:
        if proc.stdout:
            print(proc.stdout.strip())
        if proc.stderr:
            print(proc.stderr.strip())
        print(f"warning: review cache refresh failed for {folder}")


def synchronize_scaffold_readme(folder: str) -> bool:
    """Render the fresh README through the canonical paper-status projection."""

    cmd = [
        sys.executable,
        str(Path(__file__).resolve().with_name("sync_paper_status.py")),
        "--repo",
        str(ROOT),
        "--paper",
        folder,
    ]
    try:
        proc = subprocess.run(
            cmd, cwd=str(ROOT), check=False, capture_output=True, text=True
        )
    except OSError as exc:
        print(f"error: could not synchronize scaffold README for {folder}: {exc}", file=sys.stderr)
        return False
    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout).strip()
        print(
            f"error: could not synchronize scaffold README for {folder}: {detail}",
            file=sys.stderr,
        )
        return False
    if proc.stdout:
        print(proc.stdout.strip())
    return True


def download_pdf(url: str, target: Path, force: bool) -> bool:
    if target.exists() and not force:
        print(f"skip existing {target.relative_to(ROOT)}")
        return True
    try:
        request = urllib.request.Request(
            normalize_pdf_url(url),
            headers={"User-Agent": "AppliedModelingLib paper intake"},
        )
        with urllib.request.urlopen(request, timeout=60) as response:
            data = response.read()
        target.write_bytes(data)
        print(f"downloaded {target.relative_to(ROOT)}")
        return True
    except Exception as exc:  # noqa: BLE001 - intake should report and continue
        print(f"warning: could not download PDF from {url}: {exc}", file=sys.stderr)
        return False


def extract_text(pdf: Path, txt: Path, force: bool) -> bool:
    """Run pdftotext and report whether this call wrote the text artifact."""

    if txt.exists() and not force:
        print(f"skip existing {txt.relative_to(ROOT)}")
        return False
    if not pdf.exists():
        print(
            f"warning: no PDF at {pdf.relative_to(ROOT)}; skipping text extraction",
            file=sys.stderr,
        )
        return False
    if shutil.which("pdftotext") is None:
        print(
            "warning: `pdftotext` not found; skipping text extraction", file=sys.stderr
        )
        return False
    subprocess.run(["pdftotext", str(pdf), str(txt)], cwd=ROOT, check=True)
    print(f"extracted {txt.relative_to(ROOT)}")
    return True


def readme_text(
    args: argparse.Namespace,
    folder: str,
    targets: list[StatementTarget] | None = None,
) -> str:
    targets = targets or []
    title = args.title or "[Paper Title]"
    authors = args.authors or "[Authors]"
    version = args.version or "[Conference/Journal/arXiv version]"
    official_url = args.official_url or args.url
    pdf_url = normalize_pdf_url(args.pdf_url or args.url)
    theorem_rows = "\n".join(
        f"| {target.source_item} ({target.source_location}) | "
        f"`{statement_spec_name(target)}` -> `{target.lean_name}` | "
        f"statement specification + proof stub | `PaperInterface.lean` | "
        "The transparent `...Spec : Prop` is the statement-audit target; the proof "
        "body is `by sorry`; raw-source-to-expanded-Spec judgment and premise provenance pending |"
        for target in targets
    )
    if not theorem_rows:
        theorem_rows = (
            "| No source-pinned targets supplied | `none` | not started | `none` | "
            "Do not add a generic `True` theorem; extract exact source statements first |"
        )
    return f"""# {title}

## Source Version

- Paper: *{title}*
- Authors: {authors}
- Version formalized: {version}
- Official URL: {official_url}
- Public PDF: {pdf_url}

Without a statement spec, a downloaded PDF is cached as `source.pdf` and ignored
by Git. A statement spec's SHA-256-verified source bytes are copied to a stable
paper-local `source-audited.*` path recorded in `audit/paper_statement_map.json`.
These artifacts are ignored by default. Unignore one only after an explicit
redistribution-rights review; machines without the private bytes must leave the
source-evidence gate unresolved rather than accepting the digest alone.
The extracted text cache is `source.txt` when `pdftotext` succeeds, and is also
ignored by Git in public workspaces unless redistribution rights have been
checked separately.

## Paper-Facing Ledger

- Implementation theorem file: `{folder}/MainTheorems.lean`
- Source-semantic interface: `{folder}/PaperInterface.lean`
- Proof-endpoint interface: `{folder}/ProofInterface.lean`
- Machine-readable status source: `{folder}/status.json`
- Private outside-Lean proof plan: `{folder}/docs/FORMALIZATION_PLAN.md`
- Final validation report: `{folder}/FINAL_VALIDATION_REPORT.md`
- Dependency DAG: `{folder}/docs/DependencyDAG.tex`
- Rendered DAG: `{folder}/docs/DependencyDAG.pdf`
- LLM/source audit sidecars: `{folder}/audit/*.json`

`PaperInterface.lean` should be readable on its own: expose actual source
definitions/models and one transparent statement specification for each
selected source claim. Put each distinct theorem/lemma proof endpoint in
`ProofInterface.lean`, with a short closed proof that calls into
`MainTheorems.lean`. Do not duplicate the proof endpoint in the semantic
interface. Do not mark a row `formalized` unless the endpoint is closed and the
remaining assumptions cell is `None`.
Keep the dashboard surface curated but complete for source-labelled formal
material: definitions, formulas, propositions, theorems/corollaries, named
claims, and main-text lemmas that a reviewer or LLM-as-judge should inspect.
Do not omit source-visible named material merely to keep the dashboard compact.
Inventory every named appendix theorem, corollary, lemma, and definition under
the paper's single `closeout_review_policy`. The prospective default gives all
named theory an initial source-to-Lean review and repeats terminal adversarial
review for main-text material plus any explicitly promoted appendix item that
governs it. Record one complete content-pinned `source_region_partition`; do not
infer a tier from a Lean name, helper name, or proof location. Catalog
unnumbered prose assertions separately. They are claim-bearing but are not
independent theorem targets under named-theory scope unless the chosen policy
explicitly selects all prose.

Use the controlled status vocabulary from `../../docs/STATUS.md`. Public-facing
rows should use `partially formalized` for results that still depend on an
external theorem, certificate, or proof boundary, and should name that boundary
in the final column rather than using `conditional` as a separate status label.
Keep theorem/status content synchronized with the current Lean graph before
marking a row `formalized`. The planner creates the final Dependency DAG later,
from that stable graph. Keep `status.json` as the source of truth for review
rows, artifact paths, and the paper's top-level public status.

## Current Workflow

1. Byte-pin the exact source version and complete the source-only inventory,
   formula sanity pass, scope decisions, shared-library search, and
   `docs/FORMALIZATION_WORKING_MEMO.md`.
2. Put actual source models/definitions and one complete transparent
   `<name>Spec : Prop` per selected source claim in `PaperInterface.lean`.
   Put its distinct theorem/lemma endpoint in `ProofInterface.lean`; use
   `by sorry` only as a temporary private proof body.
3. Run the one non-certifying architecture pre-pass, repair role confusion or
   hidden result packages, and materialize the reviewed source map from
   `audit/v11_source_map_preparation_config.json`.
4. Prove the fixed Specs with targeted Lean builds. Record possible source
   clarifications, genuine additional assumptions, and proof deviations in the
   working memo; it is a lead log, not evidence.
5. Begin or resume audit and closeout with
   `python3 scripts/closeout_reuse_plan.py --paper {folder}` and execute only
   its `next_action`.

The current semantic judge compares the ordered byte-pinned source-anchor
bundle directly with the fully expanded transparent Spec emitted by Lean. A
Lean-to-TeX translation, curator paraphrase, theorem name, wrapper theorem,
source-map summary, or code location is never semantic evidence. The same
standard applies to material paper-local and reusable-library prerequisites;
Lean's graph owns recursive declarations, premises, proof routes, instances,
and axiom closure.

Do not generate legacy `lean_to_tex_llm.json`,
`statement_match_llm.json`, `review_surface_llm.json`,
`paper_coverage_llm.json`, `source_record_audit.json`, or
`source_record_match_llm.json` for this current-protocol paper. The planner
schedules current graph acquisition, semantic-review deltas, complete
tracked-module elaboration, theorem realization, final holistic source review,
terminal report/DAG/status work, and the one issuer-protected strict
transaction.

The dashboard and PDF packet are optional human-review presentations generated
from the current graph after the source map and interfaces are stable. Human
annotations may not be fabricated or auto-closed, but missing annotations do
not block Lean closeout.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
{theorem_rows}

## Intake Checklist

- [ ] Pin the exact source bytes and version.
- [ ] Complete the source-only selected-presentation and material-atom inventory.
- [ ] Complete the outside-Lean formula/dependency sanity pass and working memo.
- [ ] Search Mathlib, Cslib, Optlib, AppliedModelingLib, and relevant upstream
      Lean sources before introducing paper-local abstractions.
- [ ] Create actual source definitions/models and one transparent Spec per
      selected claim in `PaperInterface.lean`.
- [ ] Create each distinct proof endpoint in `ProofInterface.lean`.
- [ ] Run the architecture pre-pass and repair role confusion before freezing
      the source map and beginning expensive proof work.
- [ ] Keep final validation reports and Dependency DAGs absent until the
      planner schedules terminal closeout documents.

## Closeout Checklist

- [ ] Start with `python3 scripts/closeout_reuse_plan.py --paper {folder}` and
      execute only its current `next_action`.
- [ ] Resolve every raw-source-to-expanded-Spec, material-prerequisite,
      assumption, proof-route, axiom, realization, and source-coverage finding.
- [ ] Let the complete tracked-module checkpoint use the Git-owned module
      inventory and one dependency-aware `lake --rehash build` transaction.
- [ ] When `complete_terminal_closeout_documents` is scheduled, write the
      final report and paper-facing DAG from the current graph, compile and
      visually inspect the DAG, update paper-local status, and replan.
- [ ] Complete the independent holistic source audit only after the final
      source/interface/proof surface is fixed. Record each required distinct
      reviewer and exact audit-document hash in
      `docs/FINAL_ADVERSARIAL_REVIEW_PANEL.json`; a later count increase keeps
      valid prior entries for unchanged comparison material and adds only the
      missing review.
- [ ] Run only the exact strict worker command printed for the frozen plan.
      Acceptance exists only when that in-process transaction publishes the
      accepted obligation graph.
- [ ] Generate the packet/dashboard from the accepted current graph for optional
      human review; never manufacture reviewer annotations.
"""


def status_text(
    args: argparse.Namespace,
    folder: str,
    targets: list[StatementTarget] | None = None,
) -> str:
    targets = targets or []
    review_names = statement_first_review_names(targets)
    spec_proof_routes = statement_first_spec_proof_routes(targets)
    title = args.title or "[Paper Title]"
    authors = args.authors or "[Authors]"
    version = args.version or "[Conference/Journal/arXiv version]"
    return (
        json.dumps(
            {
                "schema": 1,
                "id": folder,
                "title": title,
                "authors": authors,
                "source_version": version,
                # New work uses the curator-owned source-inventory decision plan.
                # Historical status files retain their recorded intake authority.
                "source_inventory_review_required": True,
                # New work is private until a separate reviewed export explicitly
                # changes this release authorization.
                "repository_visibility": "private_only",
                "build_target": f"lake build +{folder}",
                "status": "not started",
                "main_caveat": "Replace with the public caveat or state that no caveat is known.",
                "human_summary": "Replace with a concise public-facing note; leave empty for formalized papers unless a source-version or proof-route note matters.",
                "human_summary_review": {
                    "status": "draft",
                    "note": (
                        "Set to human_approved only after a human has written or explicitly approved this "
                        "summary; do not rewrite a human_approved summary without explicit human instruction."
                    ),
                },
                "review_entrypoint": f"papers/{folder}/FINAL_VALIDATION_REPORT.md",
                "human_review": {
                    "reviewed_rows": 0,
                    "total_rows": 0,
                    "stale_rows": 0,
                    "mismatch_rows": 0,
                    "source": "paper-local status.json review_surface; human entries come from dashboard logs",
                },
                "paper_interface": {
                    "path": f"papers/{folder}/PaperInterface.lean",
                    "line_count": 0,
                    "declaration_rows": len(review_names),
                    "review_rows": len(review_names),
                    "oversized": False,
                    "maintainability_issue": None,
                },
                "artifacts": {
                    "paper_interface": f"papers/{folder}/PaperInterface.lean",
                    "proof_interface": f"papers/{folder}/ProofInterface.lean",
                    "assumptions": f"papers/{folder}/Assumptions.lean",
                    "final_validation_report": f"papers/{folder}/FINAL_VALIDATION_REPORT.md",
                    "dependency_dag_tex": f"papers/{folder}/docs/DependencyDAG.tex",
                    "dependency_dag_pdf": f"papers/{folder}/docs/DependencyDAG.pdf",
                    "source_proof_fidelity": f"papers/{folder}/audit/source_proof_fidelity.json",
                    "defect_support_match": f"papers/{folder}/audit/defect_support_match_llm.json",
                    "library_semantic_review": f"papers/{folder}/audit/library_semantic_review.json",
                    "v11_raw_source_spec_screening": f"papers/{folder}/audit/v11_raw_source_spec_screening.json",
                },
                "review_surface": {
                    "source_file": f"papers/{folder}/PaperInterface.lean",
                    "proof_module": f"{folder}.ProofInterface",
                    "proof_file": f"papers/{folder}/ProofInterface.lean",
                    "assumption_source_file": f"papers/{folder}/Assumptions.lean",
                    # This is a closeout requirement. A `not started` scaffold has
                    # no atom inventory or closure receipt yet, so the v11 lane
                    # remains pending until the paper reaches a full status.
                    "require_v11_raw_source_spec_screening": True,
                    "llm_statement_review": {
                        "library_semantic_review_file": f"papers/{folder}/audit/library_semantic_review.json",
                        "v11_screening_file": f"papers/{folder}/audit/v11_raw_source_spec_screening.json",
                        "defect_support_judgment_file": f"papers/{folder}/audit/defect_support_match_llm.json",
                        "assumption_judgment_file": f"papers/{folder}/audit/assumption_match_llm.json",
                        "require_explicit_source_routes": True,
                        "require_source_claim_atoms": True,
                        "require_direct_expression_semantics_review": "v1",
                        "required_prompt_version": "statement-match-v11-verbatim-source-anchor-lean-expanded-spec-claim-atoms-supporting-declarations-v4",
                        "policy": (
                            "For one source claim, give the LLM only the ordered byte-pinned source "
                            "anchor bundle plus any byte-pinned semantic context, and the fully "
                            "expanded transparent `...Spec : Prop`. Never compare a source-map "
                            "summary, curator paraphrase, theorem label, Lean-to-TeX translation, "
                            "or proof wrapper. Record the raw source-input bundle digest and the "
                            "expanded-Spec digest under the v11 protocols. The paired theorem/lemma "
                            "lives in ProofInterface.lean and receives only Lean-Meta exact-type "
                            "proof credit through the configured proposition_spec_proofs route. "
                            "For every material reused AppliedModelingLib definition that appears in a source-facing "
                            "Spec, separately register an exact bounded library declaration and source-map "
                            "item in library_semantic_review.json; compare the raw source bundle with that "
                            "actual library code, never with its name or a glossary. "
                            "For formalized closeout, independently inventory every material source "
                            "atom from exact pinned source quote bytes before consulting Lean, then "
                            "compare the resulting exact source bundle directly with the elaborated "
                            "transparent Spec. The builder-issued Lean graph separately owns the exact "
                            "Spec/proof relation and the complete recursive semantic, proof, instance, "
                            "and axiom closure. Do not issue an atom-to-component bridge worksheet or "
                            "terminal-node disposition ledger, and do not grant automatic data, "
                            "container, or name-based semantic credit. "
                            "Boolean check equals true remains proof debt when the check decides a "
                            "result-bearing proposition; reflection makes that debt visible but does "
                            "not discharge it. A total data selector may support an unconditional "
                            "theorem only about its actual internally selected output; the review must "
                            "expose its success/fallback equations and nontriviality and must not infer "
                            "that a proposed nonfallback output is accepted. A result-level dependent "
                            "if remains conditional proof debt, and a noncomputable decision receives "
                            "no executable or runtime credit. Extra replay, "
                            "certificate, process, bridge, source-row, or broad package assumptions "
                            "must be judged "
                            "`mismatch` or `uncertain`. Record the model/agent validator metadata "
                            "for the direct raw-source-to-expanded-Spec judgment. For every source route, "
                            "pin the canonical source-item key, "
                            "statement digest, exact locator, route kind, and semantic scope/evidence. "
                            "Use direct only for an exact equivalent paper-facing endpoint with an exact "
                            "source-conclusion/Lean-conclusion equivalence. Composite rows list every scoped "
                            "source component as source_component with semantic evidence and a Lean conclusion, "
                            "not a fabricated full-theorem equivalence. source_model_convention routes only an "
                            "explicit source model reading, defect_or_remark_support only a quarantined defect or "
                            "support-only remark, and proof_support only a substantive source-support scope that "
                            "never supplies endpoint credit. Declaration "
                            "links are only a cross-check, never semantic evidence. Conditional boundaries may account for extra Lean assumptions "
                            "but cannot excuse unmatched source conclusions. "
                            "Iterate on PaperInterface.lean until the full statement matches."
                        ),
                    },
                    "llm_assumption_review": {
                        "assumption_judgment_file": f"papers/{folder}/audit/assumption_match_llm.json",
                        "policy": (
                            "Every paper-facing theorem premise not derived from prior Lean declarations "
                            "must be declared in Assumptions.lean, listed in assumption_names, "
                            "and judged by an independent LLM as a true paper/source model assumption rather "
                            "than a proof assumption."
                        ),
                    },
                    "semantic_model_review": {
                        "schema": SEMANTIC_MODEL_REVIEW_SCHEMA,
                        "required_dimensions": list(SEMANTIC_MODEL_DIMENSION_ORDER),
                        "policy": (
                            "For every reviewed row, preserve an alpha-normalized expanded "
                            "binder/domain surface, including transparent local type aliases, "
                            "record parameter domains, and model records reached only in result "
                            "quantifiers. An unexpanded local opaque/constant type requires a "
                            "checked carrier/refinement bridge rather than being silently treated "
                            "as an ordinary carrier. When an expanded finite carrier uses index "
                            "arithmetic such as Fin (n + c), record the source cardinal parameter, "
                            "the expanded Lean expression, and a proved parameter translation; "
                            "then explicitly compare it with pinned source text. "
                            "Review endpoint support/cutoffs, product or iid laws versus "
                            "source state evolution, conditioning/calibration semantics, expectation "
                            "definedness, null-cell totalization and finite/countable/arbitrary "
                            "partition scope, and Real versus extended-rate codomains when the "
                            "expanded model makes them relevant. For a probability-law surface, "
                            "state whether conditioning is pointwise, a.e., positive-fiber, or "
                            "event-calibrated; state measurability/integrability or extended-value "
                            "conventions for every expectation; and expose every zero-mass-cell "
                            "branch. Local declaration and binder names are routing only; detected "
                            "probability/rate shapes need a checked bridge from source primitives. "
                            "The current graph-native review applies these dimensions directly to "
                            "every generated row whose expanded semantics trigger them; an unresolved "
                            "model dimension blocks both full statuses."
                        ),
                    },
                    "source_proof_fidelity_review": {
                        "ledger_file": f"papers/{folder}/audit/source_proof_fidelity.json",
                        "policy": (
                            "Audit source proof steps by source locator and mathematical claim, not by Lean declaration name. "
                            "Completed papers use ledger schema 2. Every defect records status_impact as formalized_note, "
                            "formalized_with_caveat, or partially_formalized plus a semantic rationale. Minor repairs with "
                            "an unchanged substantive endpoint are notes; formalized with caveat is reserved for a substantial "
                            "central source-paper error with a fully proved corrected endpoint; weaker Lean targets and added "
                            "non-source assumptions are partial. Keep this configured ledger whenever "
                            "explicit source routes or source-defect links are present; a formalized note "
                            "cannot waive an added non-source assumption or a partial boundary."
                        ),
                    },
                    "assumption_policy": "strict",
                    "assumption_names": [],
                    "source_definition_names": [],
                    "proposition_spec_proofs": spec_proof_routes,
                    "paper_coverage_required": False,
                    "include_names": review_names,
                    "slices": [
                        {
                            "id": "all",
                            "title": "All source-facing review rows",
                            "names": review_names,
                        }
                    ],
                },
            },
            indent=2,
            ensure_ascii=False,
        )
        + "\n"
    )


def paper_statement_map_text(
    args: argparse.Namespace,
    folder: str,
    spec: StatementSpec,
    source_artifact_path: str,
) -> str:
    """Seed pinned source routing without claiming independent source curation."""

    source_url = args.official_url or args.url
    items = {
        target.lean_name: {
            "statement": target.source_statement,
            "source_item": target.source_item,
            "source_kind": target.source_kind,
            "source_location": target.source_location,
            "source_url": source_url,
            "source_status": (
                "pinned statement-spec transcription; independent source audit pending"
            ),
            "spec_lean_declarations": [statement_spec_name(target)],
            "proof_lean_declarations": [target.lean_name],
            "semantic_contract_template": statement_first_semantic_contract_template(
                target
            ),
        }
        for target in spec.targets
    }
    return (
        json.dumps(
            {
                "schema": 1,
                "paper": folder,
                "source_url": source_url,
                "source_version": spec.source_version,
                "source_artifact_path": source_artifact_path,
                "source_artifact_sha256": spec.source_artifact_sha256,
                "source_inventory_kind": "pinned_statement_target_scaffold",
                "source_curated": False,
                "seed_scaffold": True,
                "source_coverage_mode": "named_theoretical_statements",
                "semantic_contract_policy": {
                    "schema": 1,
                    "activation": (
                        "Before Lean drafting, independently inventory every material source atom "
                        "against exact pinned source quote bytes; do not infer that inventory from "
                        "declaration, binder, field, or function names. After a source item has an "
                        "audited paper-local specification and a theorem/lemma proving or refuting "
                        "it, add top-level semantic_contract_schema: 1 and semantic_route_schema: 2, "
                        "classify every item with an explicit claim_bearing Boolean, and record a "
                        "semantic_contract for each source result. Route a source definition, "
                        "algorithm, model, assumption, or condition as source_semantic_declaration "
                        "to the actual paper/library prerequisite used by the result Specs; never "
                        "manufacture a theorem that merely restates a definition. At formalized "
                        "closeout, also add source_claim_atoms_schema: 1 and complete the current "
                        "raw-source-to-expanded-Spec review. Do not add a separate "
                        "source_spec_correspondence worksheet, atom-to-component bridge ledger, "
                        "or terminal-node disposition ledger: the builder-issued Lean graph owns "
                        "the exact Spec/proof relation and complete recursive semantic and axiom "
                        "closure, including proof and instance arguments. "
                        "Each statement-first row supplies an inactive "
                        "semantic_contract_template pairing its transparent `...Spec : Prop` "
                        "with its theorem/lemma. Promote that exact template only after the "
                        "independent source audit passes, the theorem has exactly the transparent "
                        "Spec type, the closure record passes, and the proof hole is replaced. Do "
                        "not manufacture a contract from the temporary by-sorry statement skeleton "
                        "alone. Historical receipts remain readable records but cannot replace the "
                        "current accepted obligation graph. For a source-game result whose feasible-action "
                        "equilibrium comparison uses a conditional/posterior or "
                        "observation-contingent value, add the separately byte-pinned "
                        "`semantic_context_requirements` kind "
                        "`strategic_observation_totality`; it requires an explicit "
                        "off-path/zero-probability totality audit and cannot be satisfied "
                        "by a Lean-only default value."
                    ),
                    "required_fields": [
                        "spec_declaration",
                        "evidence_declaration",
                        "evidence_mode",
                        "semantic_shape",
                    ],
                    "evidence_modes": ["proves", "refutes"],
                    "semantic_shapes": ["plain"],
                    "shape_policy": (
                        "Only plain exact-proposition contracts are currently enforced. "
                        "Do not record a specialized runtime, preprocessing, or refinement "
                        "shape until the audit implements its structural check."
                    ),
                    "source_defect_routing": (
                        "Every repaired_in_lean source-proof defect must be linked from a "
                        "successfully checked contract item through source_defect_ids."
                    ),
                },
                "items": items,
            },
            indent=2,
            ensure_ascii=False,
        )
        + "\n"
    )


def source_inventory_review_config_text(
    folder: str,
    spec: StatementSpec | None,
    namespace: str,
) -> str:
    """Seed the sole prospective source-inventory decision-plan container.

    The scaffold records no curator decision or derived digest.  The formalizer
    completes this one plan after the source-only mechanical and holistic
    inventory passes; ``prepare_v11_source_map.py`` then derives exact anchors,
    classifications, and inventory identities into the canonical map.
    """

    targets = spec.targets if spec is not None else ()
    return (
        json.dumps(
            {
                "schema": 1,
                "paper": folder,
                "namespace": namespace,
                "paper_interface_module": "",
                "semantic_route_schema": 2,
                "closeout_review_policy": resolve_closeout_review_policy().projection(),
                "source_version": spec.source_version if spec is not None else "",
                "include_specs": [
                    statement_spec_name(target) for target in targets
                ],
                "source_item_for_spec": {
                    statement_spec_name(target): target.lean_name
                    for target in targets
                },
                "evidence_declaration_for_spec": {
                    statement_spec_name(target): f"{namespace}.{target.lean_name}"
                    for target in targets
                },
                "source_semantic_declarations": {},
                "paper_semantic_prerequisite_sources": {},
                "library_semantic_prerequisite_sources": {},
                "semantic_context_requirements": {},
                "model_convention_ids_by_source_item": {},
                "source_named_result_inventory_review": {
                    "complete": False,
                    "validator": "",
                    "method": "",
                    "validated_at": "",
                    "prose_definition_presentations": [],
                    "candidate_presentations": [],
                    "source_region_partition": {
                        "complete": False,
                        "validator": "",
                        "method": "",
                        "validated_at": "",
                        "regions": [],
                        "source_item_regions": {},
                        "candidate_presentation_regions": {},
                        "prose_definition_presentation_regions": {},
                        "promoted_source_items": [],
                    },
                },
            },
            indent=2,
            ensure_ascii=False,
        )
        + "\n"
    )


def library_semantic_review_text(folder: str) -> str:
    """Scaffold the source-to-library semantic-review lane for a new paper."""

    return (
        json.dumps(
            {
                "schema": 1,
                "paper": folder,
                "prompt_version": "library-statement-match-v1-verbatim-source-anchor-expanded-definition",
                "target_protocol": "expanded_library_definition_v1",
                "comment": (
                    "For every material reusable AppliedModelingLib definition used by a source-facing "
                    "Spec, record the exact declaration and a source-map item. Compare only that "
                    "item's byte-pinned verbatim source bundle with the exact bounded library Lean "
                    "definition. A name, docstring, glossary, Lean-to-TeX prose, or theorem label "
                    "is not semantic input. Leave a primitive absent until an exact source connection "
                    "is identified; do not manufacture a matches judgment."
                ),
                "items": {},
            },
            indent=2,
        )
        + "\n"
    )


def v11_raw_source_spec_screening_text(folder: str) -> str:
    """Scaffold the canonical raw-source-to-expanded-Spec screening ledger."""

    return (
        json.dumps(
            {
                "schema": 3,
                "paper": folder,
                "audit_kind": "raw_source_to_expanded_spec_screening",
                "prompt_version": "statement-match-v11-verbatim-source-anchor-lean-expanded-spec-claim-atoms-supporting-declarations-v4",
                "validator": "",
                "validated_at": "",
                "comment": (
                    "Each row must compare only the exact byte-pinned source-anchor bundle "
                    "and required source context with one direct expanded PaperInterface "
                    "Spec plus Lean-emitted parameter, assumption, and terminal-conclusion "
                    "atoms. The paired proof endpoint is separate Lean evidence. Reissue with "
                    "scripts/reissue_v11_raw_source_spec_screening.py after an explicit "
                    "reviewer decision; do not enter a map summary, theorem name, wrapper, "
                    "or Lean-to-TeX paraphrase as semantic input."
                ),
                "items": {},
            },
            indent=2,
        )
        + "\n"
    )


def defect_support_match_llm_text(folder: str) -> str:
    """Create the independent exact-hash defect-to-Lean judgment scaffold."""

    return (
        json.dumps(
            {
                "schema": 1,
                "paper": folder,
                "prompt_version": "defect-support-v1-exact-source-defect-to-lean-semantic",
                "audit_kind": "source_defect_to_lean_llm",
                "source_grounded": True,
                "validator": "",
                "validator_type": "",
                "validated_at": "",
                "comment": "Judge whether each proposed Lean theorem is mathematically a counterexample to or refutation of the exact validated source defect. Names and declaration kind are never sufficient evidence.",
                "prompt_summary": [
                    "Read the exact source span and all semantic fields of the cited audit/source_proof_fidelity.json defect, then inspect the elaborated Lean signature rather than relying on the declaration name.",
                    "Copy the exact canonical source item key, source statement digest, complete source_defect snapshot, source defect digest, Lean statement text/digest, and lean_signature_sha256. Any source or Lean change must make the judgment stale.",
                    "List every elaborated signature atom exactly once in lean_obligations using signature_ref, role, signature_atom_sha256, defect_relevance, and a substantive semantic_explanation. Do not insert unpinned Lean prose in place of signature atoms.",
                    "Align every Lean atom to a semantic source_defect field. For the conclusion, use counterexample_to or refutes and explicitly align it to source_claim. For each parameter or assumption, explain the concrete witness, source-model condition, or checked derivation that prevents a hidden premise.",
                    "Reject True, reflexive equality/equivalence, vacuous implications, and statements that only share names or terminology with the defect. A theorem proof is support only when its actual conclusion and inputs establish the recorded counterexample/refutation.",
                    "Use a validator independent of the formalizer, source curator, coverage classifier, and statement judge.",
                ],
                "item_schema": {
                    "required": [
                        "source_item",
                        "source_statement_sha256",
                        "defect_id",
                        "source_defect",
                        "source_defect_sha256",
                        "support_declaration",
                        "lean_statement",
                        "lean_statement_sha256",
                        "lean_signature_sha256",
                        "judgment",
                        "reason",
                        "lean_obligations",
                        "obligation_alignment",
                    ],
                    "judgment_values": [
                        "valid_counterexample",
                        "valid_refutation",
                        "does_not_support",
                        "uncertain",
                    ],
                    "source_defect_fields": [
                        "id",
                        "source_locator",
                        "source_claim",
                        "defect_kind",
                        "affected_source_locators",
                        "statement_impact",
                        "status_impact",
                        "status_impact_rationale",
                        "repair_obligation",
                        "acceptance_condition",
                        "resolution",
                        "resolution_evidence",
                    ],
                    "lean_obligation_required": [
                        "signature_ref",
                        "role",
                        "signature_atom_sha256",
                        "defect_relevance",
                        "semantic_explanation",
                    ],
                    "alignment_required": [
                        "source_defect_field",
                        "lean_signature_ref",
                        "relation",
                        "semantic_basis",
                        "witness_or_derivation",
                    ],
                },
                "items": {},
            },
            indent=2,
            ensure_ascii=False,
        )
        + "\n"
    )


def assumption_match_llm_text(folder: str) -> str:
    return (
        json.dumps(
            {
                "schema": 1,
                "paper": folder,
                "prompt_version": "assumption-provenance-v4-verbatim-source-anchor-exact-premise",
                "validator": "",
                "validator_type": "",
                "validated_at": "",
                "comment": "Validate every assumption declaration and every Lean-emitted proposition-valued claim atom against source text or a Lean derivation.",
                "prompt_summary": [
                    "For each Assumptions.lean declaration, decide semantically whether it is an explicit paper/model assumption, a source theorem condition, a documented caveat, a partial-formalization boundary, not a paper assumption, or uncertain.",
                    "For every proposition-valued assumption atom emitted by Lean for a source-facing claim, give an independent premise_judgments entry. Group-level approval is insufficient, and comments or pretty-printed Lean text are not premise-discovery authority.",
                    "Scrutinize each premise against the source model, not by declaration name, theorem label, or phrase overlap. Expand named predicates/wrappers enough to identify the actual mathematical assumption.",
                    "Certificate, replay, process, bridge, source-row, or broad package premises need a specific source primitive or a Lean-checked instantiation path from paper primitives; otherwise mark partial_boundary/not_paper_assumption.",
                    "Use source_text_model_primitive, source_text, or paper_condition only for premises explicitly stated by the source. Supply the exact byte-pinned source-anchor quote bundle, cite source_location, and record source_anchor_quote_identity_sha256; do not use a paraphrase, map statement, or reconstructed context as source evidence.",
                    "Use derived_from_source_primitives only when the Lean development derives the premise from prior source primitives.",
                    "Displayed formulas, capacity equations, threshold identities, density/mass rows, source-row packages, certificates, and proof conveniences are not paper assumptions unless the source explicitly assumes them; otherwise mark partial_boundary or not_paper_assumption.",
                ],
                "items": {},
            },
            indent=2,
        )
        + "\n"
    )


def source_proof_fidelity_text(
    folder: str,
    source_artifact_path: str = "",
    source_artifact_sha256: str = "",
) -> str:
    """Create the source-proof fidelity ledger required for new paper closeout.

    The ledger is intentionally about source proof mathematics rather than Lean
    declaration names.  It gives a later proof agent a source-located repair
    obligation and prevents a broken proof line from being relabeled as a
    paper assumption.
    """

    return (
        json.dumps(
            {
                "schema": 1,
                "paper": folder,
                "source_artifact_path": source_artifact_path,
                "source_artifact_sha256": source_artifact_sha256,
                "review_status": "not_started",
                "reviewed_proof_scopes": [],
                "model_conventions": [],
                "checked_proof_steps": [],
                "model_convention_entry_schema": {
                    "required": [
                        "id",
                        "source_locator",
                        "classification",
                        "formal_meaning",
                        "why_needed",
                        "checked_scope",
                    ],
                    "optional": ["unresolved_relation_to_literal_source"],
                },
                "checked_proof_step_entry_schema": {
                    "required": [
                        "id",
                        "source_locator",
                        "source_step",
                        "checked_conclusion",
                        "scope",
                    ]
                },
                "defects": [],
                "defect_entry_schema": {
                    "required": [
                        "id",
                        "source_locator",
                        "source_claim",
                        "defect_kind",
                        "affected_source_locators",
                        "statement_impact",
                        "repair_obligation",
                        "acceptance_condition",
                        "resolution",
                        "resolution_evidence",
                    ],
                    "defect_kind_values": [
                        "algebra_or_sign",
                        "inequality_direction",
                        "quantifier_or_uniformity",
                        "domain_or_endpoint",
                        "index_or_integrality",
                        "event_or_measure",
                        "normalization_or_scaling",
                        "logical_dependency",
                        "other",
                    ],
                    "statement_impact_values": [
                        "proof_only",
                        "source_statement",
                        "uncertain",
                    ],
                    "status_impact_values": [
                        "formalized_note",
                        "formalized_with_caveat",
                        "partially_formalized",
                    ],
                    "resolution_values": [
                        "repaired_in_lean",
                        "open_proof_obligation",
                        "corrected_source_statement",
                        "resolved_in_current_source",
                    ],
                },
                "policy": [
                    "Review source proof text by exact source locator and mathematical claim; Lean declaration names are navigation only and are not evidence.",
                    "Give every defect a stable unique id using letters, digits, dot, underscore, or hyphen so source-map contracts can route its repair without depending on Lean names.",
                    "A source proof defect is not a paper/model assumption. Do not classify its repaired conclusion as validated_source_assumption.",
                    "Record every explicit formalization convention that resolves a source-model ambiguity in model_conventions, with the literal source relation and checked scope. A convention is not a literal source theorem without a source-side semantic bridge.",
                    "Record every source proof step independently checked by Lean in checked_proof_steps, including its exact source step, checked conclusion, and scope. A finite/event-level step does not silently establish an arbitrary-space, pointwise-conditioning, or arbitrary-partition claim.",
                    "For every defect, record the mathematical repair obligation and acceptance condition. Resolve it by a Lean derivation, leave it as an explicit open proof obligation, or record an explicit corrected source statement.",
                    "For every defect, separately record status_impact and status_impact_rationale. statement_impact says which source text changed; status_impact says whether the issue is a formalized note, a substantial source-paper caveat with a fully proved correction, or a partial-formalization boundary.",
                    "A proof-only defect may coexist with a source-faithful final theorem only after the replacement derivation is proved. A minor source-statement repair may also be formalized_note when the substantive advertised endpoint is unchanged. Only a substantial central source-paper error with a fully proved corrected endpoint justifies formalized_with_caveat.",
                ],
            },
            indent=2,
            ensure_ascii=False,
        )
        + "\n"
    )


def main_theorems_text(title: str, namespace: str) -> str:
    display_title = title or "[Paper Title]"
    return f"""import Mathlib

/-!
# Paper-Facing Theorems: {display_title}

This file is the implementation theorem layer for the source paper. Keep
source-faithful definitions and theorem wrappers here, and expose only the
compact human-review subset in `PaperInterface.lean`.

During the statement-first phase, each exact paper-facing proposition lives in a
transparent `<name>Spec : Prop` declaration in `PaperInterface.lean`; the paired
theorem/lemma endpoint belongs in `ProofInterface.lean` and has exactly that
type. Add proof implementations here only after those specifications pass v11
raw-source-to-expanded-Spec review and recursive premise provenance audit. Before full closeout, the v11
realization audit independently binds pinned source atoms to the elaborated Spec
and accounts for the complete Lean closure; a proof hole or a declaration name
is never evidence for that correspondence.
-/

namespace {namespace}

end {namespace}
"""


def assumption_source_text(title: str, folder: str, namespace: str) -> str:
    display_title = title or "[Paper Title]"
    return f"""import {folder}.MainTheorems

/-!
# Paper Assumptions: {display_title}

This file is the only paper-local place for assumptions that are not derived in
Lean. Keep it small. Each declaration must be explicitly stated by the paper,
listed in `status.json` `review_surface.assumption_names`, and judged in
`audit/assumption_match_llm.json` as a true source/model assumption rather than a
proof convenience.

The audit discovers proposition-valued theorem premises from Lean's elaborated
claim manifests. Do not add `audit-premise` comments or duplicate a binder in a
sidecar to make it discoverable; instead, keep the proposition explicit in the
source-facing `Spec` and route any reusable paper assumption through this
module and `status.json`.

Start empty. Add a proposition here only after locating it as a literal source
antecedent. Never move an unproved lemma or target conclusion here merely to
make a statement skeleton compile.
-/

namespace {namespace}

end {namespace}
"""


def paper_interface_text(
    title: str,
    folder: str,
    namespace: str,
    targets: list[StatementTarget] | None = None,
) -> str:
    targets = targets or []
    display_title = title or "[Paper Title]"
    inventory = "\n".join(
        f"- `{statement_spec_name(target)}` -> `{target.lean_name}`: "
        f"{target.source_item}, {target.source_location}."
        for target in targets
    )
    if not inventory:
        inventory = (
            "- None yet. This interface is intentionally empty because no "
            "source-pinned statement spec was supplied."
        )

    declarations: list[str] = []
    for target in targets:
        lean_type = "\n  ".join(target.lean_type.splitlines())
        declarations.append(
            f"""/--
{target.source_item}

Paper statement: {target.source_statement}

Source location: {target.source_location}
Source status: pinned statement-spec transcription; independent source audit pending

This transparent proposition is the exact statement-audit target. It is not
proof evidence. Its exact-type proof endpoint is declared in
`ProofInterface.lean`, so this human-facing file presents the full semantic
proposition once. At closeout, source atoms must be independently inventoried
from pinned source quote bytes and bound to this elaborated proposition rather
than inferred from identifiers.
-/
def {statement_spec_name(target)} : Prop :=
  {lean_type}"""
        )
    declaration_text = "\n\n".join(declarations)
    if not declaration_text:
        declaration_text = (
            "-- Intentionally no theorem placeholder: extract and audit the exact "
            "source targets first."
        )
    return f"""import {folder}.MainTheorems
import {folder}.Assumptions

/-!
# Human-Facing Paper Interface: {display_title}

This is the compact Lean file a human should read after formalization to check
whether the paper's definitions and named theorem statements were represented
correctly. Keep the row-level dashboard and LLM audit statements in this file
for every paper. Move implementation details, proof aliases, and bulky helper
lemmas behind imported modules such as `AuditInterface.lean`, but expose the
audited paper-facing statements directly here; do not use
`paper_interface.audit_surface_path`.

Rules for completing this file:

- Keep the paper's definitions/formatted objects first, in source order.
- Expose the actual paper formulas here; do not only point to generic library
  definitions or implementation witnesses.
- A material reusable `AppliedModelingLib` primitive may remain a reference here only
  after `audit/library_semantic_review.json` records its exact bounded library
  declaration and an explicit byte-pinned paper-source connection. The
  dashboard and human-review packet show and source-check that declaration
  before the dependent Spec; a library name, docstring, or glossary is not a
  semantic bridge. Do not add a duplicate paper claim merely to restate it.
- If a named theorem needs a hypothesis that is not derived from earlier Lean
  declarations, declare that hypothesis in `Assumptions.lean` and list it in
  `status.json` `review_surface.assumption_names`.
- Then state the named results directly, with assumptions visible in each
  theorem signature by referencing named paper assumptions imported from
  `Assumptions.lean`.
- In the statement-first phase, write every complete source-facing statement as
  a transparent `<name>Spec : Prop` here, exactly once. Put the paired
  theorem/lemma of that exact type in `ProofInterface.lean`; its temporary
  proof body may be `by sorry` only in a private draft. This separation keeps
  the human semantic surface free of thin wrapper declarations.
- Before drafting that Lean surface, independently inventory every material
  source atom from exact pinned source quote bytes. Do not infer source atoms
  from declaration, binder, field, function, or source-map names.
- Run raw-source-to-expanded-Spec statement matching plus Lean-emitted
  premise/conclusion claim-atom review on the skeleton. The semantic comparison uses
  only byte-pinned source quotes (and separately pinned source context) against
  the expanded transparent Spec; map summaries and proof wrappers are not
  semantic inputs. Then freeze each canonical Lean declaration-manifest digest.
- In the proof phase, replace the `ProofInterface.lean` `sorry` with a short
  proof that calls into `MainTheorems.lean` or lower proof files without
  changing the specification or theorem type. Any specification/type change
  invalidates the freeze and requires a fresh statement audit.
- At formalized closeout, complete the v11 realization receipt: Lean Meta checks
  the theorem has exactly the transparent Spec type; each source atom is bound
  to the elaborated Spec surface; closure traversal includes proof and instance
  arguments; and every material terminal has a source, approved correction or
  additional assumption, checked derivation, or version-pinned foundation
  disposition. No data, container, or identifier-based exemption is allowed.
- The transparent `...Spec` is the sole semantic-review target for its source
  claim. The paired theorem/lemma is a proof endpoint whose exact Spec type is
  verified by Lean Meta, not a duplicate source-to-Lean comparison row.
- Keep proof endpoints, exhaustive endpoint aliases, and proof-seam checks in
  `ProofInterface.lean`, implementation modules, or `ProofLedger.lean`, not
  here. Do not create new `PostPaperAudit.lean` or `AuditLedger.lean` files;
  those names are legacy.

## Named Results

Each entry has one semantic-review target (`Spec`) and one proof endpoint (the
paired theorem/lemma). The human dashboard and review packet present that pair
once rather than treating the two declarations as duplicate paper claims.

{inventory}
-/

namespace {namespace}

{declaration_text}

end {namespace}
"""


def proof_interface_text(
    title: str,
    folder: str,
    namespace: str,
    targets: list[StatementTarget] | None = None,
) -> str:
    """Render the non-human proof endpoints paired with PaperInterface Specs."""

    targets = targets or []
    display_title = title or "[Paper Title]"
    declarations = "\n\n".join(
        f"""/--
Lean proof endpoint for `{statement_spec_name(target)}`.

This theorem is intentionally outside `PaperInterface.lean`: Lean Meta checks
that it has exactly the transparent Spec type, while source-to-Lean semantic
review compares the raw source bundle only to that Spec.
-/
{target.kind} {target.lean_name} :
  {statement_spec_name(target)} := by
  sorry"""
        for target in targets
    )
    if not declarations:
        declarations = "-- No proof endpoint until a source-pinned Spec is added."
    return f"""import {folder}.PaperInterface

/-!
# Proof Interface: {display_title}

This file contains exact-type proof endpoints for the transparent propositions
in `PaperInterface.lean`. It is not a human semantic-review surface: one source
claim is reviewed once, against its expanded `...Spec : Prop` declaration.
-/

namespace {namespace}

{declarations}

end {namespace}
"""


def gitignore_text() -> str:
    return """source-audited*
*.pdf
!docs/DependencyDAG.pdf
*.aux
*.log
*.fls
*.fdb_latexmk
*.synctex.gz
"""


def review_launcher_text() -> str:
    return """#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd \"$(dirname \"${BASH_SOURCE[0]}\")\" && pwd)"
ROOT_DIR="$(cd \"${SCRIPT_DIR}/../..\" && pwd)"
PAPER_DIR=\"$(basename \"$SCRIPT_DIR\")\"

exec \"${ROOT_DIR}/scripts/launch_review_dashboard.sh\" --paper \"$PAPER_DIR\" \"$@\"
"""


def root_import_text(folder: str) -> str:
    return f"""import {folder}.ProofInterface
"""


def notes_text(title: str, namespace: str, args: argparse.Namespace) -> str:
    official_url = args.official_url or args.url
    title_text = title or "[Paper Title]"
    return f"""# {title_text} Formalization Notes

This is a lightweight handoff document for source-to-Lean mapping.

- Namespace: `{namespace}`
- Official URL: {official_url}
- Source PDF: `source.pdf`
- Local source text cache, if generated: `source.txt` (ignored by Git in public workspaces)

## Formalization checklist

- [ ] Full named-result inventory copied to the README theorem table.
- [ ] DAG graph includes all required paper-stage nodes and dependencies.
- [ ] README status and remaining-assumption notes match proof artifacts.
- [ ] Post-formalization library elevation pass completed: reusable proof
      results, techniques, and primitives were moved into `AppliedModelingLib` when
      local/low-risk, or recorded with destination modules in the final report.
- [ ] Recursive provenance is clear in the consolidated paper closeout. Run a
      standalone repository-wide provenance audit only for a named diagnostic
      failure or at an explicit integration/release boundary.
- [ ] Final status review completed before publishing.

## Notes

- Date reviewed:
- Last theorem row formalized:
- Outstanding assumptions / caveats:
- Reusable library elevation candidates:

"""


def working_memo_text(title: str) -> str:
    """Return the non-evidentiary source/proof issue log used during proving."""

    return f"""# Formalization Working Memo: {title or '[Paper Short Name]'}

This is a working lead log, not audit evidence and not a final validation
report. Record possible issues while reading and proving; independently verify
each retained item against the pinned source and final Lean surface during
closeout.

For every item, record the exact source location, current mathematical reading,
Lean treatment, and review state. Prefer “clarification” unless the printed
formula or statement is actually false.

## Possible Source Clarifications

- None recorded.

## Possible Printed Typos Or Errors

- None recorded.

## Possible Proof-Strategy Deviations

- None recorded.

## Possible Model Conventions Or Extra Assumptions

- None recorded.

## Deferred Formalization Or Library Work

- None recorded.
"""


def formalization_plan_text(
    title: str,
    namespace: str,
    targets: list[StatementTarget] | None = None,
    paper_root: str | None = None,
) -> str:
    targets = targets or []
    paper_root = paper_root or namespace
    title_text = title or "[Paper Title]"
    skeleton_rows = "\n".join(
        f"| {target.source_item} / {target.source_location} | "
        f"`{statement_spec_name(target)}` -> `{target.lean_name}` | "
        "pending | pending | pending | `by sorry` |"
        for target in targets
    )
    if not skeleton_rows:
        skeleton_rows = (
            "| No source-pinned target supplied | `none` | | pending | pending | none |"
        )
    return f"""# Formalization Plan: {title_text}

This is a working scratchpad for outside-Lean proof thinking. Keep it short and
useful; it is not the final validation report. Once the current source-shaped
target and audited `PaperInterface.lean` skeleton are present, prioritize the
next proof obligation; update this document at material boundaries rather than
after routine proof steps.

- Namespace: `{namespace}`

## Initial Outside-Lean Paper Audit

- Source version / local files inspected:
- Source/version mismatch notes:
- Complete named-result ledger status:
- Formula sanity check:
  - Signs, constants, normalizations, quantifiers, domains:
  - Density vs mass / likelihood-kernel representation issues:
  - Dependency map between named source results:
  - Formula-bearing displayed claims that need derivation, not source-row assumptions:
- Named result sanity check:
  - Results that look correct as stated:
  - Suspected bugs, missing assumptions, or ambiguous wording:
- Source-proof fidelity ledger (`audit/source_proof_fidelity.json`):
  - Proof scopes reviewed by source locator and mathematical claim:
  - Source proof defects, if any, with repair obligation and acceptance condition:
  - Proof-only defects kept out of `Assumptions.lean`:
- Shared-library reuse checkpoint:
  - Mathlib declarations/modules inspected:
  - Cslib declarations/modules inspected:
  - Optlib declarations/modules inspected:
  - Other potential upstream sources inspected:
  - Upstream sources used or ported, with citation/provenance:
  - Existing `AppliedModelingLib` declarations/modules inspected:
  - API chosen and near-misses:
  - Source-defined objects that will use reusable library definitions, their
    exact source routes, and their planned material-library semantic reviews:
- Proof strategy consequences:
  - Source proof route to follow:
  - Cleaner Lean route or reusable library route:
  - Major issues already reported to the user:
- Algorithmic complexity audit, when applicable:
  - Transitive operational dependency graph over every reachable branch and old semantic closure/oracle dependencies:
  - Worst-case recurrence and bound over the stated input-size measure:
  - Traversal/enumeration lengths, duplicates, and materialization/rebuild charges:
  - Representation/container primitives and rational bit-growth work accounting; missing/excluded work withholds a runtime match:
  - Pinned evidence when closure elimination is material: artifact/source hashes and semantic binding to generated IR/C or a cost-threaded executor:

## Source Inventory

- Definitions / formatted paper objects:
- Named lemmas / propositions / theorems / corollaries:
- Named assumptions / model conditions used by those results:
- Deep-only prose, standalone formulas, algorithms, figures, simulations, and
  computational examples (record scope disposition; do not create normal-mode
  proof targets merely because they are numbered or displayed):

## Reviewed Source Inventory Boundary

Do not begin the main proof campaign until this boundary is complete. The
purpose is to discover missing conclusions and hidden premises while changing
the statement skeleton is still cheap, rather than during final closeout.

- [ ] Exact source version and every source artifact used by the normal-scope
      inventory are byte-pinned.
- [ ] Complete the curator-owned
      `audit/v11_source_map_preparation_config.json`
      `source_named_result_inventory_review` plan under the procedure in
      `skills/econcs-formalizer/SKILL.md`; do not create a second
      `intake_freeze.json` authority.
- [ ] The single `closeout_review_policy` and complete content-pinned
      `source_region_partition` classify all main, appendix, and supplement
      source material before review; Lean names and proof imports do not set
      the tier.
- [ ] The independent normal-scope inventory contains every named theoretical
      definition, result, and source assumption, with explicit dispositions for
      exclusions. Navigation names are not coverage evidence.
- [ ] Every selected result has source-first premise/conclusion atoms, exact
      anchors, and one complete transparent `Spec : Prop` in `PaperInterface`.
- [ ] The proof-obligation dependency order below is acyclic and assigns one
      owning module to each result; concurrent agents do not share an item.
- [ ] One focused Lean claim-graph and raw-source statement review has frozen the exact
      statement identities. After this point, a proof-body-only edit reopens
      proof closure and compilation, not the human statement judgment.
- [ ] The dashboard cache is created once after this freeze, never during bare
      scaffold creation.

### Proof-obligation order

| Order | Source-semantic item | Dependencies | Owning module / agent | Statement frozen | Proof status |
|---:|---|---|---|---|---|
| 1 | Fill from the independent source inventory | none | | no | pending |

## Initial Proof Strategy

- Main theorem chain:
- Likely reusable `AppliedModelingLib` seams:
- Paper steps that look underspecified or analytically hard:
- Formal target map:
  - Rows to fully prove now:
  - Empirical/descriptive rows out of formal theorem scope:
  - Explicit assumption/certificate boundaries, if any:
- Planned fallback route if the source proof is too informal:

## Audited Statement Skeleton

Before drafting Lean, independently inventory every material source atom against
the exact pinned source quote bytes. Then replace the generated placeholder with
every in-scope paper-facing theorem/formula statement as a transparent
`<name>Spec : Prop`, followed by `theorem/lemma <name> : <name>Spec := by sorry`.
Audit and freeze the specification's canonical declaration-manifest digest; Lean
Meta must confirm the paired proof route has exactly that elaborated proposition.
The inactive source-map `semantic_contract_template` records only the
spec/proof pairing to promote after source review and proof completion. Never
treat the `by sorry` route, an identifier, or a type/container label as active
semantic contract or proof evidence.

At formalized closeout, complete current source-to-Spec correspondence. Bind every
source atom to the current elaborated Spec surface, traverse the full Lean
closure including proof and instance arguments, and give every material closure
terminal a source atom, approved source correction/additional assumption,
checked Lean derivation, or version-pinned foundation disposition. Reuse a
semantic judgment only when that item's source-atom content, Spec closure,
narrow closure environment, and exact theorem type are unchanged. Historical
receipts remain readable records, but only the current accepted obligation graph
is a current closeout credential.

Partition every source and Lean obligation through both the numeric and
discrete semantics reviews. Record coercion, division, rounding, normalization,
strictness, and zero-denominator behavior separately. Distinguish immediate
successor, next active choice, eventual occurrence, restricted support, and
first occurrence literally. Bind any proved equivalence to an explicit
equality/iff Lean conclusion on the reviewed obligations.

For every `source_routes` entry, pin the source item, current statement digest,
exact locator, route kind, and semantic scope/evidence. `direct` is only for an
exact equivalent paper-facing endpoint with an exact source-conclusion/Lean-
conclusion equivalence. A `corrected_source_statement` retains archival text
and has exactly one complete PaperInterface endpoint in `lean_declarations`;
state all repaired clauses as one explicit conjunction there. Aliases, proof
helpers, support declarations, and semantic bridges cannot carry the repaired
target, source-route credit, or coverage credit. A composite row lists each scoped component as
`source_component`, using a Lean conclusion as evidence without claiming a
full-theorem equivalence. `source_model_convention` is for an explicit model
reading, `defect_or_remark_support` for quarantined/support-only material, and
`proof_support` only for a substantive support scope that never gives endpoint
credit. Names route review but never establish it.

| Source item / locator | Spec -> proof route | Lean semantic identity | Statement verdict | Premise provenance | Proof body |
|---|---|---|---|---|---|
{skeleton_rows}

Signature changes after a `matches` verdict invalidate the row and require a
fresh audit. Replacing `sorry` without changing the type does not.

## Planned Verification And Invalidation

Use these boundaries throughout the paper so closeout is execution of a plan,
not a new discovery pass.

| Material change | Reopen |
|---|---|
| One source item's semantic content or byte anchor | That item's source, coverage, statement, and dependent proof obligations |
| One `Spec` type or elaborated semantic dependency | That statement item and its dependent proof closure |
| Proof body only, theorem type unchanged | Focused compilation and proof closure only |
| Report, README, status prose, or DAG only | Presentation/status consistency only |
| Audit producer or protocol | Only lanes whose pinned producer/protocol identity changed; first run the reuse planner |

Planned commands, in order:

1. Proof loop: `lake build +<TouchedPaperModule>`. At closeout, run
   `env LEAN_NUM_THREADS=1 python3 scripts/private_paper_checkpoint.py {paper_root}`
   so Lake rehashes and dependency-orders one build containing every tracked
   paper-local source module; a forced root alone may reuse stale imported
   artifacts.
2. Closeout readiness: `python3 scripts/closeout_reuse_plan.py --paper {paper_root}`.
   Execute only its `next_action`. When it requests terminal closeout documents,
   write the final report and Dependency DAG from the current reviewed graph,
   compile and inspect the DAG, update paper-local status, and replan. Do not
   create or freeze those terminal artifacts during intake or ordinary proof
   work. If the frozen plan gives an action an explicit
   state-qualified successor, continue through that successor to its required
   replan boundary; do not rerun the planner between a cache-miss build and its
   one manifest refresh. A cache miss never erases unchanged semantic judgments.
   An exact current compiled cache skips a redundant standalone build, while a
   rebuilt artifact must be replanned before strict closeout.
4. Consolidated closeout, once the planner exposes it: run the exact
   `strict_closeout` argv/command printed by the plan. It carries a
   non-authoritative operational plan identity, preventing an accidental
   duplicate of the same completed execution. Do not invoke
   `run_paper_closeout.py` from a handwritten command: its planner-issued
   identity and any `--new-run` disposition are required.
   This command records ignored operational state under `.review_traces`; if
   the terminal stream disappears, inspect that state instead of starting a
   duplicate run.
5. Run a repository-wide status/site refresh only at an integration or release
   boundary, not as part of every paper proof closeout.

## Reusable-Library TODO

- Library APIs to use directly:
- Small reusable lemmas to add now:
- Larger reusable components to defer:
- Library-audit risks:

## Execution Checklist

- [ ] Download/cache source PDFs and text extracts, with redistribution notes.
- [ ] Complete the normal named-theory inventory and record deep-only
      dispositions separately.
- [ ] During active source-map repair, run `--source-inventory-check` before a
      necessary manifest refresh. With a current cache, use targeted
      statement/coverage checks; after the source map, interface, and status
      surface are stable, refresh once and let bounded manifest retry/fallback
      handle outliers. At frozen closeout, do not repeat those commands by
      default: let the planner schedule the required delta.
- [ ] Fill the formal target map and declare any intended boundary/certificate.
- [ ] Build or select reusable library APIs before adding paper-local wrappers.
- [ ] Replace the paper scaffold with complete source-facing Lean definitions,
      transparent `<name>Spec : Prop` statements, and theorem/lemma routes typed
      exactly by those specifications; use `by sorry` only for temporary private
      proof bodies.
- [ ] Independently inventory every material source atom from exact pinned quote
      bytes before Lean review. At full closeout, bind those atoms to the
      elaborated Spec and account for every material closure terminal, including
      proof and instance arguments; no declaration, data, or container category
      is an automatic exemption.
- [ ] Run the current Lean-owned recursive closure, premise-provenance, and raw
      byte-pinned-source-to-expanded-Spec reviews on every skeleton claim;
      record and freeze each semantic identity. The paired theorem is only
      proof evidence, not a second semantic match.
- [ ] Complete numeric and discrete obligation partitions; do not claim absence
      when the elaborated manifest exposes arithmetic or list operations.
- [ ] Complete the applicable fidelity-risk dimensions from expanded semantics:
      output/conclusion shape, action or input space, witness/optimization
      semantics, cardinality/quantification, and, for executable results,
      input scope, state transitions, termination, numeric representation, cost,
      and the global-claim bridge.
- [ ] For every runtime claim, audit the transitive operational dependency graph
      over every reachable branch; refinement alone is not cost evidence. Give a
      worst-case recurrence and bound, and completely account for traversal,
      duplicates, materialization, representation primitives, and rational bit
      growth. Missing or excluded work withholds a runtime match; materially
      eliminated closure dependencies need artifact/source hashes and semantic
      binding to generated IR/C or a cost-threaded executor.
- [ ] Review every source proof route used; record source proof defects as
      mathematical repair obligations, never as source assumptions.
- [ ] Prove all rows marked in-scope, or downgrade them with an explicit
      boundary note.
- [ ] Replace every skeleton `sorry` without changing its audited specification
      or theorem type; rerun statement audit whenever either changes.
- [ ] At closeout, run the reuse planner and let its terminal-document action
      schedule the README, paper-local status, DAG, and validation-report update
      from the same current row list.
- [ ] Freeze the paper inputs only after those requested documents are current.
      Let the planner's
      ordered actions own the targeted paper build, audits,
      placeholder/provenance checks, and DAG validation; do not pre-run those
      gates just to recreate an intermediate receipt.
- [ ] Record any unresolved source bug, assumption, or library debt.

## Active Scratchpad

- Current Lean endpoint:
- Exact current mathematical gap:
- Next bridge lemmas to try:
- Informal proof sketch / recurrence / construction:

## Issue And Deviation Log

Record possible source clarifications, printed errors, proof-strategy
deviations, model conventions, and extra assumptions in
`docs/FORMALIZATION_WORKING_MEMO.md`. This plan may name the active proof seam,
but it is not a second issue ledger. The working memo is a lead log, not audit
evidence; independently verify every retained item during closeout.
"""


def final_validation_report_text(title: str, folder: str) -> str:
    title_text = title or "[Paper Short Name]"
    template = (PAPERS / "TEMPLATE" / "FINAL_VALIDATION_REPORT.md").read_text(
        encoding="utf-8"
    )
    return template.replace(
        "# Final Validation Report: [Paper Short Name]",
        f"# Final Validation Report: {title_text}",
        1,
    ).replace("papers/TEMPLATE", f"papers/{folder}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "url", help="paper URL; arXiv abs URLs are converted to PDF URLs"
    )
    parser.add_argument(
        "--folder", help="citation-style folder name, e.g. ABC24ShortTitle"
    )
    parser.add_argument("--title", help="paper title for README and theorem ledger")
    parser.add_argument("--authors", help="paper authors for README")
    parser.add_argument(
        "--version", help="source version, conference, journal, or arXiv version"
    )
    parser.add_argument(
        "--official-url", help="canonical paper URL if different from input URL"
    )
    parser.add_argument("--pdf-url", help="direct PDF URL if different from input URL")
    parser.add_argument(
        "--namespace", help="Lean namespace; defaults to sanitized folder name"
    )
    parser.add_argument(
        "--statement-spec",
        type=Path,
        help=(
            "JSON file containing exact theorem targets plus a verified local source artifact; "
            "target types are validated against the imported AppliedModelingLib surface; without it "
            "PaperInterface.lean is intentionally empty"
        ),
    )
    parser.add_argument(
        "--no-download",
        action="store_true",
        help="scaffold files without downloading the PDF",
    )
    parser.add_argument(
        "--force", action="store_true", help="overwrite existing scaffold files"
    )
    parser.add_argument(
        "--with-notes",
        action="store_true",
        help="generate PAPER_NOTES.md handoff checklist",
    )
    parser.add_argument(
        "--refresh-cache",
        action="store_true",
        help=(
            "build the dashboard cache immediately; normally defer this until the "
            "source inventory and PaperInterface statement skeleton are frozen"
        ),
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    folder = args.folder or derive_folder(args.url)
    namespace = args.namespace or lean_namespace(folder)
    try:
        validate_scaffold_cli_inputs(args, folder, namespace)
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    statement_spec: StatementSpec | None = None
    if args.statement_spec is not None:
        try:
            statement_spec = load_statement_spec(args.statement_spec)
        except ValueError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 2
        if not args.version or PLACEHOLDER_RE.search(args.version):
            print("error: --version is required with --statement-spec", file=sys.stderr)
            return 2
        if args.version.strip() != statement_spec.source_version:
            print(
                "error: --version does not match statement spec source_version",
                file=sys.stderr,
            )
            return 2
    targets = statement_spec.targets if statement_spec is not None else []

    paper_dir = PAPERS / folder
    paper_dir.mkdir(parents=True, exist_ok=True)
    docs_dir = paper_dir / "docs"
    audit_dir = paper_dir / "audit"
    docs_dir.mkdir(exist_ok=True)
    audit_dir.mkdir(exist_ok=True)

    pdf = paper_dir / "source.pdf"
    txt = paper_dir / "source.txt"
    audited_source: Path | None = None

    if statement_spec is not None:
        audited_source = paper_dir / audited_source_filename(
            statement_spec.source_artifact_path
        )
        if audited_source.exists() and not args.force:
            existing_sha256 = hashlib.sha256(audited_source.read_bytes()).hexdigest()
            if existing_sha256 != statement_spec.source_artifact_sha256:
                print(
                    f"error: existing {audited_source.relative_to(ROOT)} does not match statement spec artifact",
                    file=sys.stderr,
                )
                return 2
        elif statement_spec.source_artifact_path.resolve() != audited_source.resolve():
            shutil.copyfile(statement_spec.source_artifact_path, audited_source)
            print(
                f"copied verified source artifact to {audited_source.relative_to(ROOT)}"
            )
        copied_sha256 = hashlib.sha256(audited_source.read_bytes()).hexdigest()
        if copied_sha256 != statement_spec.source_artifact_sha256:
            print(
                "error: copied source artifact failed SHA-256 verification",
                file=sys.stderr,
            )
            return 2

    source_proof_artifact_path = ""
    source_proof_artifact_sha256 = ""
    if audited_source is not None and statement_spec is not None:
        source_proof_artifact_path = str(audited_source.relative_to(ROOT))
        source_proof_artifact_sha256 = statement_spec.source_artifact_sha256
        if audited_source.suffix.lower() == ".pdf":
            extract_text(audited_source, txt, True)

    rendered_interface = paper_interface_text(
        args.title or "", folder, namespace, targets
    )
    rendered_proof_interface = proof_interface_text(
        args.title or "", folder, namespace, targets
    )
    try:
        validate_rendered_statement_interface(namespace, targets, rendered_interface)
        validate_rendered_proof_interface(
            namespace, targets, rendered_proof_interface
        )
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    write_file(paper_dir / ".gitignore", gitignore_text(), args.force)
    write_file(paper_dir / "README.md", readme_text(args, folder, targets), args.force)
    write_file(
        paper_dir / "status.json", status_text(args, folder, targets), args.force
    )
    write_file(
        audit_dir / "library_semantic_review.json",
        library_semantic_review_text(folder),
        args.force,
    )
    write_file(
        audit_dir / "v11_raw_source_spec_screening.json",
        v11_raw_source_spec_screening_text(folder),
        args.force,
    )
    write_file(
        audit_dir / "defect_support_match_llm.json",
        defect_support_match_llm_text(folder),
        args.force,
    )
    write_file(
        audit_dir / "assumption_match_llm.json",
        assumption_match_llm_text(folder),
        args.force,
    )
    write_file(
        audit_dir / "source_proof_fidelity.json",
        source_proof_fidelity_text(
            folder,
            source_proof_artifact_path,
            source_proof_artifact_sha256,
        ),
        args.force,
    )
    if statement_spec is not None:
        copied_source_path = str(audited_source.relative_to(ROOT))
        write_file(
            audit_dir / "paper_statement_map.json",
            paper_statement_map_text(
                args,
                folder,
                statement_spec,
                copied_source_path,
            ),
            args.force,
        )
    write_file(
        audit_dir / "v11_source_map_preparation_config.json",
        source_inventory_review_config_text(folder, statement_spec, namespace),
        args.force,
    )
    launch_script = paper_dir / "review-dashboard.sh"
    write_file(
        launch_script,
        review_launcher_text(),
        args.force,
    )
    launch_script.chmod(0o755)
    write_file(
        docs_dir / "FORMALIZATION_PLAN.md",
        formalization_plan_text(
            args.title or "", namespace, targets, paper_root=folder
        ),
        args.force,
    )
    write_file(
        docs_dir / "FORMALIZATION_WORKING_MEMO.md",
        working_memo_text(args.title or ""),
        args.force,
    )
    write_file(
        paper_dir / "MainTheorems.lean",
        main_theorems_text(args.title or "", namespace),
        args.force,
    )
    write_file(
        paper_dir / "Assumptions.lean",
        assumption_source_text(args.title or "", folder, namespace),
        args.force,
    )
    write_file(
        paper_dir / "PaperInterface.lean",
        rendered_interface,
        args.force,
    )
    write_file(
        paper_dir / "ProofInterface.lean",
        rendered_proof_interface,
        args.force,
    )
    write_file(PAPERS / f"{folder}.lean", root_import_text(folder), args.force)
    if args.with_notes:
        write_file(
            paper_dir / "PAPER_NOTES.md",
            notes_text(args.title or "", namespace, args),
            args.force,
        )

    if statement_spec is None and not args.no_download:
        downloaded = download_pdf(args.pdf_url or args.url, pdf, args.force)
        if downloaded:
            extract_text(pdf, txt, args.force)
    elif statement_spec is None:
        print("skipped PDF download")

    if statement_spec is None:
        print(
            "no --statement-spec supplied; PaperInterface.lean contains no theorem placeholder"
        )

    if not synchronize_scaffold_readme(folder):
        return 2

    if getattr(args, "refresh_cache", False):
        refresh_review_cache(folder)
    else:
        print(
            "deferred dashboard cache: freeze the source inventory and "
            "PaperInterface first, then run `python3 scripts/review_dashboard.py "
            f"--paper {folder} --refresh-cache` once"
        )

    print(f"paper scaffold ready: {paper_dir.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
