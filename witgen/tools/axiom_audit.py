"""Fail-closed audit of an exact list of Lean theorem declarations."""

import re
from collections import Counter

ALLOWED_AXIOMS = {"propext", "Quot.sound"}


def check_axioms(text, expected, *, allowed_axioms=None):
    """Check exact coverage; alternate trust policies must be explicit per call."""
    allowed = ALLOWED_AXIOMS if allowed_axioms is None else set(allowed_axioms)
    if not expected or len(expected) != len(set(expected)):
        raise ValueError("expected axiom declarations must be nonempty and unique")
    pattern = (
        r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
    )
    reports = re.findall(pattern, text)
    observed = [name for name, _ in reports]
    if Counter(observed) != Counter(expected):
        raise ValueError(
            f"axiom report coverage mismatch: expected {expected!r}, got {observed!r}"
        )
    dependencies = {
        name.strip() for _, deps in reports for name in deps.split(",") if name.strip()
    }
    if dependencies - allowed:
        raise ValueError(
            f"unexpected axiom dependencies: {sorted(dependencies - allowed)!r}"
        )
    return sorted(dependencies)
