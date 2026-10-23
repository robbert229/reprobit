"""Audit the pinned MSVC 5.0 upstream revisions and regenerate committed authorities.

Every declared profile path is checked against the checked-out pinned revision,
then file size/digest authorities and portable-tree-v1 tree receipts are
recomputed with the library's own authority code. The script writes
``src/reprobit/msvc50_authorities.py`` with ``--write`` and otherwise fails if
the committed module differs from the audit.

With ``--fetch`` any missing checkout is created by fetching its pinned
revision, so one command fetches and verifies. Without ``--fetch`` an
existing exact checkout is required::

    python scripts/audit_msvc50_authorities.py --checkouts-root msvc50-upstream --fetch
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import subprocess
import sys
from pathlib import Path

from reprobit.toolchains import (
    MSVC_50_RTM,
    MSVC_50_SP1,
    MSVC_50_SP2,
    MSVC_50_SP3,
    ToolchainProfile,
    portable_tree_receipt,
    profile,
)

REPO_ROOT = Path(__file__).resolve().parent.parent

PROFILE_IDENTIFIERS = (MSVC_50_RTM, MSVC_50_SP1, MSVC_50_SP2, MSVC_50_SP3)
CMAKE_FRONTEND_PATH = "bin/nmake.exe"
AUTHORITIES_MODULE = REPO_ROOT / "src" / "reprobit" / "msvc50_authorities.py"


class AuditError(RuntimeError):
    """A pinned revision does not satisfy the profile it claims to supply."""


def _repository_name(url: str) -> str:
    return url.rsplit("/", 1)[-1].removesuffix(".git")


def _verify_checkout(checkout: Path, revision: str) -> None:
    received = subprocess.run(
        ("git", "-C", str(checkout), "rev-parse", "HEAD"),
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    if received != revision:
        raise AuditError(
            f"checkout {checkout.name} is at {received}, not pinned {revision}; "
            "fetch the pinned revision and detach onto it"
        )


def _file_authority(root: Path, relative: str) -> tuple[int, str]:
    path = root.joinpath(*relative.split("/"))
    if not path.is_file() or path.is_symlink():
        raise AuditError(f"{root.name}: declared file is absent or redirected: {relative}")
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    return path.stat().st_size, digest


def _tree_authority(root: Path, relative: str) -> dict[str, int | str]:
    tree = root.joinpath(*relative.split("/"))
    if not tree.is_dir() or tree.is_symlink():
        raise AuditError(f"{root.name}: declared tree is absent or redirected: {relative}")
    receipt = portable_tree_receipt(tree, relative)
    return {
        "entries": receipt.entry_count,
        "max_depth": receipt.max_depth,
        "membership_sha256": receipt.membership_sha256,
        "content_sha256": receipt.content_sha256,
    }


def _declared_files(installation_profile: ToolchainProfile) -> tuple[str, ...]:
    source = installation_profile.sources[0]
    files = tuple(sorted(path for path in source.paths if path.startswith("bin/")))
    if set(files) != set(installation_profile.required_producers) | set(
        installation_profile.required_runtime_files
    ):
        raise AuditError("declared files drifted from the profile producer/runtime sets")
    return files


def _declared_trees(installation_profile: ToolchainProfile) -> tuple[str, ...]:
    trees = tuple(
        sorted(installation_profile.include_roots) + sorted(installation_profile.library_roots)
    )
    if set(trees) != {
        path for path in installation_profile.sources[0].paths if not path.startswith("bin/")
    }:
        raise AuditError("declared trees drifted from the profile source paths")
    return trees


def _fetch_checkout(checkout: Path, repository: str, revision: str) -> None:
    checkout.mkdir(parents=True)
    for step in (
        ("init", "--quiet"),
        ("config", "core.autocrlf", "false"),
        ("config", "advice.detachedHead", "false"),
        ("remote", "add", "origin", repository),
    ):
        subprocess.run(("git", "-C", str(checkout), *step), check=True, capture_output=True)
    subprocess.run(
        ("git", "-C", str(checkout), "fetch", "--quiet", "--depth=1", "origin", revision),
        check=True,
        capture_output=True,
    )
    subprocess.run(
        ("git", "-C", str(checkout), "checkout", "--quiet", "--detach", "FETCH_HEAD"),
        check=True,
        capture_output=True,
    )
    _verify_checkout(checkout, revision)


def _ensure_checkout(checkout: Path, repository: str, revision: str, fetch: bool) -> None:
    if checkout.is_dir():
        _verify_checkout(checkout, revision)
        return
    if fetch:
        _fetch_checkout(checkout, repository, revision)
        return
    raise AuditError(
        f"no checkout for {repository} under the root; fetch the pinned revision "
        f"{revision} or rerun with --fetch"
    )


def audit_profile(
    checkouts_root: Path, installation_profile: ToolchainProfile, *, fetch: bool = False
) -> dict[str, dict[str, object]]:
    source = installation_profile.sources[0]
    checkout = checkouts_root / _repository_name(source.repository)
    _ensure_checkout(checkout, source.repository, source.revision, fetch)
    return {
        "files": {
            relative: _file_authority(checkout, relative)
            for relative in _declared_files(installation_profile)
        },
        "trees": {
            relative: _tree_authority(checkout, relative)
            for relative in _declared_trees(installation_profile)
        },
        "cmake_frontend": {CMAKE_FRONTEND_PATH: _file_authority(checkout, CMAKE_FRONTEND_PATH)},
    }


def _format_authorities(audited: dict[str, dict[str, dict[str, object]]]) -> str:
    lines = [
        '"""Reviewed byte authorities for every MSVC 5.0 toolchain profile.',
        "",
        "Each release's authorities were audited against the pinned archaic-msvc",
        "revision recorded on its profile. File authorities record installed size",
        "and SHA-256; tree authorities are portable-tree-v1 receipts, matching",
        "what a toolchain lock records for the same tree. Regenerate and re-audit",
        "with scripts/audit_msvc50_authorities.py --write; treat any change here",
        "as a reviewed decision.",
        '"""',
        "",
        "from __future__ import annotations",
        "",
        "from dataclasses import dataclass",
        "",
        "",
        "@dataclass(frozen=True, slots=True)",
        "class Msvc50FileAuthority:",
        '    """One installed file: exact size and content digest."""',
        "",
        "    size: int",
        "    sha256: str",
        "",
        "",
        "@dataclass(frozen=True, slots=True)",
        "class Msvc50TreeAuthority:",
        '    """One portable-tree-v1 receipt for an input tree."""',
        "",
        "    entries: int",
        "    max_depth: int",
        "    membership_sha256: str",
        "    content_sha256: str",
        "",
        "",
    ]
    sections = (
        ("files", "MSVC50_FILE_AUTHORITIES"),
        ("trees", "MSVC50_TREE_AUTHORITIES"),
        ("cmake_frontend", "MSVC50_CMAKE_FRONTEND_AUTHORITIES"),
    )
    for section, attribute in sections:
        if attribute == "MSVC50_CMAKE_FRONTEND_AUTHORITIES":
            lines.extend(
                [
                    "# bin/nmake.exe is not a profile-declared path: profile validation admits",
                    "# producers, runtime files, and input trees only, and the MSVC 4.2",
                    "# provisioner likewise supplies NMAKE outside profile sources. This table",
                    "# therefore anchors to the provisioned-files convention; byte verification",
                    "# belongs to the provisioner's verify path rather than to a profile",
                    "# declaration. Revisit this anchor if 5.0 provisioning ever declares it.",
                ]
            )
        lines.append(f"{attribute} = {{")
        for identifier in PROFILE_IDENTIFIERS:
            result = audited[identifier]
            lines.append(f'    "{identifier}": {{')
            for relative, authority in sorted(result[section].items()):
                if isinstance(authority, tuple):
                    size, digest = authority
                    lines.extend(
                        [
                            f'        "{relative}": Msvc50FileAuthority(',
                            f"            {size},",
                            f'            "{digest}",',
                            "        ),",
                        ]
                    )
                else:
                    assert isinstance(authority, dict)
                    lines.extend(
                        [
                            f'        "{relative}": Msvc50TreeAuthority(',
                            f"            {authority['entries']},",
                            f"            {authority['max_depth']},",
                            f'            "{authority["membership_sha256"]}",',
                            f'            "{authority["content_sha256"]}",',
                            "        ),",
                        ]
                    )
            lines.append("    },")
        lines.append("}")
        lines.append("")
    return "\n".join(lines)


def load_committed_authorities(path: Path) -> dict[str, dict[str, dict[str, object]]]:
    """Load the committed module as an audited-form mapping for comparison."""
    spec = importlib.util.spec_from_file_location("reprobit_msvc50_authorities", path)
    if spec is None or spec.loader is None:
        raise AuditError(f"cannot import committed authorities: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    tables = {
        "files": module.MSVC50_FILE_AUTHORITIES,
        "trees": module.MSVC50_TREE_AUTHORITIES,
        "cmake_frontend": module.MSVC50_CMAKE_FRONTEND_AUTHORITIES,
    }
    loaded: dict[str, dict[str, dict[str, object]]] = {}
    for identifier in PROFILE_IDENTIFIERS:
        loaded[identifier] = {}
        for section, table in tables.items():
            entries: dict[str, object] = {}
            for relative, authority in table[identifier].items():
                fields = {
                    field_name: getattr(authority, field_name)
                    for field_name in authority.__dataclass_fields__
                }
                if section in ("files", "cmake_frontend"):
                    entries[relative] = (fields["size"], fields["sha256"])
                else:
                    entries[relative] = {
                        "entries": fields["entries"],
                        "max_depth": fields["max_depth"],
                        "membership_sha256": fields["membership_sha256"],
                        "content_sha256": fields["content_sha256"],
                    }
            loaded[identifier][section] = entries
    return loaded


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkouts-root", type=Path, required=True)
    parser.add_argument(
        "--fetch",
        action="store_true",
        help="create missing checkouts by fetching their pinned revisions",
    )
    parser.add_argument(
        "--write", action="store_true", help="write the regenerated module into src/reprobit/"
    )
    parser.add_argument("--output", type=Path, default=AUTHORITIES_MODULE)
    args = parser.parse_args(argv)

    audited: dict[str, dict[str, dict[str, object]]] = {}
    for identifier in PROFILE_IDENTIFIERS:
        result = audit_profile(args.checkouts_root, profile(identifier), fetch=args.fetch)
        audited[identifier] = result
        print(
            f"{identifier}: audited {len(result['files'])} files and {len(result['trees'])} trees"
        )
    if args.write:
        args.output.write_text(_format_authorities(audited), encoding="utf-8")
        formatted = subprocess.run(
            ("ruff", "format", "--quiet", str(args.output)),
            check=False,
            capture_output=True,
            text=True,
        )
        if formatted.returncode != 0 and formatted.stderr:
            print(formatted.stderr, file=sys.stderr)
        print(f"wrote {args.output}")
        return 0

    committed = load_committed_authorities(args.output)
    if committed != audited:
        for identifier in PROFILE_IDENTIFIERS:
            for section in ("files", "trees", "cmake_frontend"):
                if committed[identifier][section] != audited[identifier][section]:
                    print(
                        f"{identifier}: committed {section} differ from the audited upstream",
                        file=sys.stderr,
                    )
        return 1
    print("committed authorities match the audited upstream revisions")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
