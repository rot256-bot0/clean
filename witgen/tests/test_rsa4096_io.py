from pathlib import Path
import unittest

from tools.rsa4096.io import FIELD_PRIME, decode_public_inputs, decode_witness


class Rsa4096IOTests(unittest.TestCase):
    def fixture(self):
        return {
            "modulus": "80" + "00" * 511,
            "signature": "00" * 511 + "07",
            "digest": "00" * 31 + "03",
        }

    def test_fixed_big_endian_adapter_does_no_rsa_computation(self):
        self.assertEqual(decode_public_inputs(self.fixture()),
                         {"modulus": str(1 << 4095), "signature": "7", "digest": "3"})

    def test_bad_public_shapes_and_alphabet_are_rejected(self):
        for key in ["modulus", "signature", "digest"]:
            for bad in ["", "0", "gg" * (512 if key != "digest" else 32), True]:
                with self.subTest(key=key, bad=str(bad)[:10]):
                    row = self.fixture()
                    row[key] = bad
                    with self.assertRaises(ValueError):
                        decode_public_inputs(row)
        row = self.fixture()
        row["modulus"] = "00" * 512
        with self.assertRaises(ValueError):
            decode_public_inputs(row)

    def test_raw_canonical_witnesses_are_preserved(self):
        payload = {"witness": ["0", str(FIELD_PRIME - 1), "7"]}
        self.assertEqual(decode_witness(payload, expected_count=3), [0, FIELD_PRIME - 1, 7])

    def test_raw_witnesses_are_rejected_never_normalized(self):
        for bad in [str(FIELD_PRIME), str(FIELD_PRIME + 1), "-1", "+1", "01", " 1", 1, True, None]:
            with self.subTest(bad=bad):
                with self.assertRaises(ValueError):
                    decode_witness({"witness": [bad]}, expected_count=1)
        for payload in [{}, {"witness": []}, {"witness": ["0", "1"]}, {"witness": "0"}]:
            with self.assertRaises(ValueError):
                decode_witness(payload, expected_count=1)


if __name__ == "__main__":
    unittest.main()
