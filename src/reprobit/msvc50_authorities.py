"""Reviewed byte authorities for every MSVC 5.0 toolchain profile.

Each release's authorities were audited against the pinned archaic-msvc
revision recorded on its profile. File authorities record installed size
and SHA-256; tree authorities are portable-tree-v1 receipts, matching
what a toolchain lock records for the same tree. Regenerate and re-audit
with scripts/audit_msvc50_authorities.py --write; treat any change here
as a reviewed decision.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class Msvc50FileAuthority:
    """One installed file: exact size and content digest."""

    size: int
    sha256: str


@dataclass(frozen=True, slots=True)
class Msvc50TreeAuthority:
    """One portable-tree-v1 receipt for an input tree."""

    entries: int
    max_depth: int
    membership_sha256: str
    content_sha256: str


MSVC50_FILE_AUTHORITIES = {
    "msvc_5_0_rtm": {
        "bin/c1.dll": Msvc50FileAuthority(
            563984,
            "e519dfe6f45cc0503b7aac43d125b2f156305269b89f0dc765c40d29627c0943",
        ),
        "bin/c1xx.dll": Msvc50FileAuthority(
            1047312,
            "fea1e9fbbc2d204202f1a5ea61e5a938b17a92acda57e16dd53d4ec01c9d186b",
        ),
        "bin/c2.exe": Msvc50FileAuthority(
            630544,
            "6d1406af5f62647347cfa7175cd7e108b838d6841a546396f29252198a14d73d",
        ),
        "bin/cl.exe": Msvc50FileAuthority(
            46080,
            "bf9f9c74f756fed96e13f7f9a4273495c7dde0a1fb968e3ef6d760ad6d73dfeb",
        ),
        "bin/cvtres.exe": Msvc50FileAuthority(
            16144,
            "0f82167cd888105224463feef5cadebaef970c12932597919e3033d77ed3de6c",
        ),
        "bin/lib.exe": Msvc50FileAuthority(
            4608,
            "f8124cf4c5f0744700a4c718d79f39fa45f3781b437db4faa7d09a272ef67053",
        ),
        "bin/link.exe": Msvc50FileAuthority(
            359424,
            "279544809e6353c8e622eb88aea94e86b0258f3c4b8a976373bf4d68a41b63e1",
        ),
        "bin/msdis100.dll": Msvc50FileAuthority(
            117520,
            "c54d1bf7bc7bf321ad8a903f083f34b0f12ec984761c0280ff9a72190798c0cb",
        ),
        "bin/mspdb50.dll": Msvc50FileAuthority(
            167424,
            "06aaaca9c928bdef790259c9c30328529e10d1ec2f77da09c4ff74de7734fe69",
        ),
        "bin/rc.exe": Msvc50FileAuthority(
            7952,
            "14a84379d318c76760bd550afaece03b5e8b39b49cbf6de7e0f7f0eac8216242",
        ),
    },
    "msvc_5_0_sp1": {
        "bin/c1.dll": Msvc50FileAuthority(
            565008,
            "7f12a4a889c5a0277f12c391ca462657dc81ef7be769faf629331bd117983d5d",
        ),
        "bin/c1xx.dll": Msvc50FileAuthority(
            1049360,
            "8b66d3f14035bfa228e79d45481318457594f65ed91f87319d23932372857d8b",
        ),
        "bin/c2.exe": Msvc50FileAuthority(
            633616,
            "592c65eea2e159a8b7bf61fb20ed12fc0dfdb3c5b7179267d34634aa7a2dc6e4",
        ),
        "bin/cl.exe": Msvc50FileAuthority(
            46080,
            "bf9f9c74f756fed96e13f7f9a4273495c7dde0a1fb968e3ef6d760ad6d73dfeb",
        ),
        "bin/cvtres.exe": Msvc50FileAuthority(
            16144,
            "0f82167cd888105224463feef5cadebaef970c12932597919e3033d77ed3de6c",
        ),
        "bin/lib.exe": Msvc50FileAuthority(
            4608,
            "f8124cf4c5f0744700a4c718d79f39fa45f3781b437db4faa7d09a272ef67053",
        ),
        "bin/link.exe": Msvc50FileAuthority(
            392704,
            "e28424d3eefcdd96ecc8c3fe38d0fad3d33077c62026f7774eda90784d0eb4d9",
        ),
        "bin/msdis100.dll": Msvc50FileAuthority(
            127760,
            "2abf240e688910b903065c2c26321d1dc3aecb82186fdbee113a01c9ef3d8943",
        ),
        "bin/mspdb50.dll": Msvc50FileAuthority(
            174592,
            "730497a2cc447ad0ea91c52ed9aa1b9d21572f4ca37ce686937946c5a98f7f8c",
        ),
        "bin/rc.exe": Msvc50FileAuthority(
            7952,
            "14a84379d318c76760bd550afaece03b5e8b39b49cbf6de7e0f7f0eac8216242",
        ),
    },
    "msvc_5_0_sp2": {
        "bin/c1.dll": Msvc50FileAuthority(
            565008,
            "7f12a4a889c5a0277f12c391ca462657dc81ef7be769faf629331bd117983d5d",
        ),
        "bin/c1xx.dll": Msvc50FileAuthority(
            1049360,
            "8b66d3f14035bfa228e79d45481318457594f65ed91f87319d23932372857d8b",
        ),
        "bin/c2.exe": Msvc50FileAuthority(
            633616,
            "592c65eea2e159a8b7bf61fb20ed12fc0dfdb3c5b7179267d34634aa7a2dc6e4",
        ),
        "bin/cl.exe": Msvc50FileAuthority(
            46080,
            "bf9f9c74f756fed96e13f7f9a4273495c7dde0a1fb968e3ef6d760ad6d73dfeb",
        ),
        "bin/cvtres.exe": Msvc50FileAuthority(
            16144,
            "0f82167cd888105224463feef5cadebaef970c12932597919e3033d77ed3de6c",
        ),
        "bin/lib.exe": Msvc50FileAuthority(
            4608,
            "f8124cf4c5f0744700a4c718d79f39fa45f3781b437db4faa7d09a272ef67053",
        ),
        "bin/link.exe": Msvc50FileAuthority(
            392704,
            "e28424d3eefcdd96ecc8c3fe38d0fad3d33077c62026f7774eda90784d0eb4d9",
        ),
        "bin/msdis100.dll": Msvc50FileAuthority(
            127760,
            "2abf240e688910b903065c2c26321d1dc3aecb82186fdbee113a01c9ef3d8943",
        ),
        "bin/mspdb50.dll": Msvc50FileAuthority(
            174592,
            "730497a2cc447ad0ea91c52ed9aa1b9d21572f4ca37ce686937946c5a98f7f8c",
        ),
        "bin/rc.exe": Msvc50FileAuthority(
            7952,
            "14a84379d318c76760bd550afaece03b5e8b39b49cbf6de7e0f7f0eac8216242",
        ),
    },
    "msvc_5_0_sp3": {
        "bin/c1.dll": Msvc50FileAuthority(
            565008,
            "7f12a4a889c5a0277f12c391ca462657dc81ef7be769faf629331bd117983d5d",
        ),
        "bin/c1xx.dll": Msvc50FileAuthority(
            1051408,
            "e27df3bb9a37058c85dad3fb7d1ed30b9e52d38fb6c0f66c8fdba0a11111d3d9",
        ),
        "bin/c2.exe": Msvc50FileAuthority(
            660240,
            "e75aecaf4073b0817ffb638cae5fff636b2e2d1a090daabf8f68dbc954515fae",
        ),
        "bin/cl.exe": Msvc50FileAuthority(
            46080,
            "bf9f9c74f756fed96e13f7f9a4273495c7dde0a1fb968e3ef6d760ad6d73dfeb",
        ),
        "bin/cvtres.exe": Msvc50FileAuthority(
            15120,
            "16a45886f9257d990a9478c32ee6c1cbf4ac1fbcf889e5755960539233962465",
        ),
        "bin/lib.exe": Msvc50FileAuthority(
            4608,
            "f8124cf4c5f0744700a4c718d79f39fa45f3781b437db4faa7d09a272ef67053",
        ),
        "bin/link.exe": Msvc50FileAuthority(
            464896,
            "04c892989f4cc8076ef45e033215eb7aefbdf1459cbee9b13a81f8ddb718b579",
        ),
        "bin/msdis100.dll": Msvc50FileAuthority(
            127760,
            "2abf240e688910b903065c2c26321d1dc3aecb82186fdbee113a01c9ef3d8943",
        ),
        "bin/mspdb50.dll": Msvc50FileAuthority(
            174592,
            "730497a2cc447ad0ea91c52ed9aa1b9d21572f4ca37ce686937946c5a98f7f8c",
        ),
        "bin/rc.exe": Msvc50FileAuthority(
            7952,
            "14a84379d318c76760bd550afaece03b5e8b39b49cbf6de7e0f7f0eac8216242",
        ),
    },
}

MSVC50_TREE_AUTHORITIES = {
    "msvc_5_0_rtm": {
        "atl/include": Msvc50TreeAuthority(
            15,
            0,
            "2175161a79705c0e3b0104897c14a693f559bf1815d8cec5b087d3da798b00b2",
            "90d7bf573a5ae7912819c6bbaec80cc13177a450f64439ca35925dd717dec17b",
        ),
        "include": Msvc50TreeAuthority(
            433,
            1,
            "df015b6059a33e67e1ce85d603f1b5493af2b94c20de474ada7e97e5083f6f13",
            "3a34e828e271eac447a08e7eb5777a500da738a3e1eae345ed485aa450060a7d",
        ),
        "lib": Msvc50TreeAuthority(
            127,
            0,
            "78b81926b1520db9f3039671d29040bb7ba474f86ca0178810b57f870ff0ebd9",
            "25b6ef472975ab85ddcde9a66eb9c6ba03c3e1ece9c1658548f1b7991cb46235",
        ),
        "mfc/include": Msvc50TreeAuthority(
            147,
            1,
            "56050300a80230742614c8ad3cc254a481afef2e970d41a4d90429ef94b7ba09",
            "0fd812d8af1ab2b6af309d241d6aac852d04702e3752c979b5e62d21867cb388",
        ),
        "mfc/lib": Msvc50TreeAuthority(
            33,
            0,
            "3228decf888524908c163861ceef7e826f1668295a78127681f34def4ac6c449",
            "a45e32b9253ceab9f3e4d8625f0bd18099033176e31c10059050c4746ed81328",
        ),
    },
    "msvc_5_0_sp1": {
        "atl/include": Msvc50TreeAuthority(
            15,
            0,
            "8fb947514c3fbdf32dad80c98cb39a7f977a22cc7b0cbd962301bc2c9cca0ab5",
            "43f6c6a99138384ebba54c265366c718766927b47a4fd26c4ea0b0ac0e167872",
        ),
        "include": Msvc50TreeAuthority(
            433,
            1,
            "6a68d8a91b8298d844b3c4a55905b568978039f8730a44a2df2ce324b0326d7f",
            "3628eae276133cf171793eae3c9fec64f2b604f46a8a5d133ea41dfb73875263",
        ),
        "lib": Msvc50TreeAuthority(
            127,
            0,
            "8ecc4b8b88ac16a0d8ad1752e72b0d5f189c7810c634120eb3d67be236a85a45",
            "5cccf3dd58b65e4b8072650b45157e3e489559c1c7e83777a61bf667b0602ce4",
        ),
        "mfc/include": Msvc50TreeAuthority(
            147,
            1,
            "56050300a80230742614c8ad3cc254a481afef2e970d41a4d90429ef94b7ba09",
            "0fd812d8af1ab2b6af309d241d6aac852d04702e3752c979b5e62d21867cb388",
        ),
        "mfc/lib": Msvc50TreeAuthority(
            35,
            0,
            "9ed323d7f8a6c25662b39517366b5265260cd3fb27d8e9728279ffadbecd7304",
            "250d3fd8f825795f05e77caae4c2b5c269ae080cee13428ab9d434889d904302",
        ),
    },
    "msvc_5_0_sp2": {
        "atl/include": Msvc50TreeAuthority(
            15,
            0,
            "8fb947514c3fbdf32dad80c98cb39a7f977a22cc7b0cbd962301bc2c9cca0ab5",
            "43f6c6a99138384ebba54c265366c718766927b47a4fd26c4ea0b0ac0e167872",
        ),
        "include": Msvc50TreeAuthority(
            433,
            1,
            "6a68d8a91b8298d844b3c4a55905b568978039f8730a44a2df2ce324b0326d7f",
            "3628eae276133cf171793eae3c9fec64f2b604f46a8a5d133ea41dfb73875263",
        ),
        "lib": Msvc50TreeAuthority(
            127,
            0,
            "8ecc4b8b88ac16a0d8ad1752e72b0d5f189c7810c634120eb3d67be236a85a45",
            "5cccf3dd58b65e4b8072650b45157e3e489559c1c7e83777a61bf667b0602ce4",
        ),
        "mfc/include": Msvc50TreeAuthority(
            147,
            1,
            "56050300a80230742614c8ad3cc254a481afef2e970d41a4d90429ef94b7ba09",
            "0fd812d8af1ab2b6af309d241d6aac852d04702e3752c979b5e62d21867cb388",
        ),
        "mfc/lib": Msvc50TreeAuthority(
            35,
            0,
            "9ed323d7f8a6c25662b39517366b5265260cd3fb27d8e9728279ffadbecd7304",
            "250d3fd8f825795f05e77caae4c2b5c269ae080cee13428ab9d434889d904302",
        ),
    },
    "msvc_5_0_sp3": {
        "atl/include": Msvc50TreeAuthority(
            15,
            0,
            "39bad29880de14fd32b8a574edc657d69399b709176cddaefbefa93840a30926",
            "bea0e87cb2bfdb2b85ad93fff3412b54ccf6fbc52094b4a3454b5bbcdbcd444d",
        ),
        "include": Msvc50TreeAuthority(
            433,
            1,
            "ceb0cd5f6ebc42b08660c43ae0d71a1bdcfdbbcba18cd6b6c705eef60bae0751",
            "2225fba2dd86a88748998626ecc13db82030c28bb9b766f3973a0896d4d1ae19",
        ),
        "lib": Msvc50TreeAuthority(
            127,
            0,
            "e158fdb8207d57742bcc527d64d7cae1e9410be41c9b93c502cc75cb643276d6",
            "0b254b332f9fe272ee077f5a88ce8c4130f6b26e8cb62bab9658e257d5b8140c",
        ),
        "mfc/include": Msvc50TreeAuthority(
            147,
            1,
            "56050300a80230742614c8ad3cc254a481afef2e970d41a4d90429ef94b7ba09",
            "0fd812d8af1ab2b6af309d241d6aac852d04702e3752c979b5e62d21867cb388",
        ),
        "mfc/lib": Msvc50TreeAuthority(
            33,
            0,
            "970b8793a0509129459d7dc3b89632ea21c0e14c20f0074f3d3d3ae200503816",
            "e6be3f81ea0824366390a8815e149c3d95dd100694958fe2f5fecf2e32468502",
        ),
    },
}

# bin/nmake.exe is not a profile-declared path: profile validation admits
# producers, runtime files, and input trees only, and the MSVC 4.2
# provisioner likewise supplies NMAKE outside profile sources. This table
# therefore anchors to the provisioned-files convention; byte verification
# belongs to the provisioner's verify path rather than to a profile
# declaration. Revisit this anchor if 5.0 provisioning ever declares it.
MSVC50_CMAKE_FRONTEND_AUTHORITIES = {
    "msvc_5_0_rtm": {
        "bin/nmake.exe": Msvc50FileAuthority(
            68608,
            "db18b84da26b3a3f9762a8ec70a03d1ed4e9643d01fc9767e39355c1073e8fed",
        ),
    },
    "msvc_5_0_sp1": {
        "bin/nmake.exe": Msvc50FileAuthority(
            68608,
            "db18b84da26b3a3f9762a8ec70a03d1ed4e9643d01fc9767e39355c1073e8fed",
        ),
    },
    "msvc_5_0_sp2": {
        "bin/nmake.exe": Msvc50FileAuthority(
            68608,
            "db18b84da26b3a3f9762a8ec70a03d1ed4e9643d01fc9767e39355c1073e8fed",
        ),
    },
    "msvc_5_0_sp3": {
        "bin/nmake.exe": Msvc50FileAuthority(
            68608,
            "db18b84da26b3a3f9762a8ec70a03d1ed4e9643d01fc9767e39355c1073e8fed",
        ),
    },
}
