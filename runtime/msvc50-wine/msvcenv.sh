#!/usr/bin/env bash
#
# Copyright (c) 2018 Martin Storsjo
# Copyright (c) 2025 archaic-msvc developers
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
# WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
# MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
# ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
# WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
# ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
# OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

set -e

# Adapted for MSVC 5.00 (archaic-msvc portable layout).

MSVC_ROOT="$(cd -- "$(dirname -- "$0")/../.." && printf '%s\n' "$(pwd)")"
MSVC_ROOT=${MSVC_ROOT//\//\\}
export INCLUDE="${MSVC_ROOT}\\include;${MSVC_ROOT}\\mfc\\include;${MSVC_ROOT}\\atl\\include"
export LIB="${MSVC_ROOT}\\lib;${MSVC_ROOT}\\mfc\\lib"
export LIBPATH="$LIB"
export WINEPATH="${MSVC_ROOT}\\bin"

# Wine fidelity for the 5.0 toolchain (issue #4 finding):
#
# Every 5.00 bin tool imports MSVCRT.dll at startup; link.exe additionally
# imports IMAGEHLP.dll and msdis100.dll (which itself imports MSVCP50.dll),
# rc.exe imports RCDLL.dll, and the PDB helper mspdb50.dll is CRT-only.  Wine
# provides a builtin msvcrt.dll and imagehlp.dll; it has no builtins for
# msvcp50, rcdll, mspdb50, or msdis100, so those resolve to the provisioned
# native binaries in bin/ through WINEPATH.
#
# The byte-identity fixture proves that Wine's builtin msvcrt and imagehlp do
# NOT perturb 5.0 compiler or linker output: the same SP3 fixture certifies
# byte-identical under Wine and native Windows.  Unlike MSVC 4.2 (whose
# builtin msvcrt40/msvcrt20 qsort diverged and had to be forced native), no
# WINEDLLOVERRIDES is required here -- and one is not even possible: forcing
# msvcrt to "native" breaks Wine itself because Wine's own advapi32.dll
# depends on msvcrt.dll.  The 5.0 profiles therefore declare no Wine DLL
# overrides; this transport intentionally sets none.
export WINEDLLOVERRIDES="${WINEDLLOVERRIDES:-}"

MSVC_EDITBIN_BIN="${MSVC_ROOT}\\bin\\editbin.exe"
MSVC_NMAKE_BIN="${MSVC_ROOT}\\bin\\nmake.exe"
MSVC_CVPACK_BIN="${MSVC_ROOT}\\bin\\cvpack.exe"
MSVC_CL_BIN="${MSVC_ROOT}\\bin\\cl.exe"
MSVC_CVTRES_BIN="${MSVC_ROOT}\\bin\\cvtres.exe"
MSVC_MC_BIN="${MSVC_ROOT}\\bin\\mc.exe"
MSVC_DUMPBIN_BIN="${MSVC_ROOT}\\bin\\dumpbin.exe"
MSVC_LIB_BIN="${MSVC_ROOT}\\bin\\lib.exe"
MSVC_MIDL_BIN="${MSVC_ROOT}\\bin\\midl.exe"
MSVC_RC_BIN="${MSVC_ROOT}\\bin\\rc.exe"
MSVC_LINK_BIN="${MSVC_ROOT}\\bin\\link.exe"