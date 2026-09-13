"""Fixed public byte packing and strict raw witness validation, with no RSA arithmetic."""
import re

FIELD_PRIME = 21888242871839275222246405745257275088548364400416034343698204186575808495617
WITNESS_CELLS = 160527
CONSTRAINT_ROWS = 161242


def decode_public_inputs(row):
    if not isinstance(row, dict):
        raise ValueError("public input must be an object")
    result = {}
    for key, width in [("modulus", 512), ("signature", 512), ("digest", 32)]:
        value = row.get(key)
        if not isinstance(value, str) or len(value) != 2 * width or not re.fullmatch(r"[0-9a-fA-F]+", value):
            raise ValueError(f"{key} must encode exactly {width} big-endian bytes")
        result[key] = str(int(value, 16))
    if int(result["modulus"]).bit_length() != 4096:
        raise ValueError("modulus must have exactly 4096 bits")
    return result


def decode_witness(payload, expected_count=WITNESS_CELLS):
    if not isinstance(payload, dict) or set(payload) != {"witness"}:
        raise ValueError("expected a witness-only object")
    values = payload["witness"]
    if not isinstance(values, list) or len(values) != expected_count:
        raise ValueError(f"expected exactly {expected_count} witness cells")
    result = []
    for index, raw in enumerate(values):
        if not isinstance(raw, str) or re.fullmatch(r"0|[1-9][0-9]*", raw) is None:
            raise ValueError(f"cell {index} is not a canonical decimal string")
        value = int(raw)
        if value >= FIELD_PRIME:
            raise ValueError(f"cell {index} is not a canonical circuit-field element")
        result.append(value)
    return result
