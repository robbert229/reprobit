"""The build's authenticated compiler-helper library: the reviewed table applied.

`reprobit.classic.toolchain_helpers` reads compiler-helper bodies from a
library whose bytes match a reviewed authority; this module supplies the
reviewed one, `msvc50_authorities.MSVC50_LIBRARY_AUTHORITIES` (each digest
is the file's in its profile's reviewed ``lib`` tree).
"""

from __future__ import annotations

from pathlib import Path

from reprobit.classic.toolchain_helpers import (
    HELPER_LIBRARY,
    HelperLibrary,
    authenticate_helper_library,
)
from reprobit.msvc50_authorities import MSVC50_LIBRARY_AUTHORITIES


def reviewed_helper_library(profile: str, data: bytes) -> HelperLibrary:
    """``lib/libc.lib`` of ``profile`` from its bytes, refused unless they are the reviewed ones."""
    return authenticate_helper_library(profile, data, MSVC50_LIBRARY_AUTHORITIES)


def load_helper_library(toolchain_root: Path, profile: str) -> HelperLibrary | None:
    """The authenticated ``lib/libc.lib`` of an installed toolchain, or None.

    None when the profile has no reviewed library authority or the file is
    absent: a proof that needs a helper then refuses.  Present bytes that
    differ from the authority are refused here.
    """
    if HELPER_LIBRARY not in MSVC50_LIBRARY_AUTHORITIES.get(profile, {}):
        return None
    path = toolchain_root.joinpath(*HELPER_LIBRARY.split("/"))
    if path.is_symlink() or not path.is_file():
        return None
    return reviewed_helper_library(profile, path.read_bytes())


__all__ = ["load_helper_library", "reviewed_helper_library"]
