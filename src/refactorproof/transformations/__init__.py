from .base import CandidateRecord, Transformation, Variant
from .let_intro import LetIntro
from .helper_extract import HelperExtract

REGISTRY = {
    "T1": LetIntro,
    "T2": HelperExtract,
}


def _register_optional():
    try:
        from .algebraic_rewrite import CommutativeSwap  # noqa: F401

        REGISTRY["T3"] = CommutativeSwap
    except ImportError:
        pass
    try:
        from .conditional_invert import ConditionalInvert  # noqa: F401

        REGISTRY["T4"] = ConditionalInvert
    except ImportError:
        pass
    try:
        from .branch_extract import BranchExtract  # noqa: F401

        REGISTRY["T5"] = BranchExtract
    except ImportError:
        pass


_register_optional()


def get_transformations(keys):
    out = []
    for k in keys:
        if k not in REGISTRY:
            raise KeyError(f"unknown transformation {k}; known: {sorted(REGISTRY)}")
        out.append(REGISTRY[k]())
    return out


__all__ = ["CandidateRecord", "Transformation", "Variant", "REGISTRY", "get_transformations", "LetIntro", "HelperExtract"]
