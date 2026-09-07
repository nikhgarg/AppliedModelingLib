from __future__ import annotations

import unittest

from scripts.v11_screening_contract import (
    V11_SCREENING_PROMPT_VERSION,
    validate_v11_screening_container,
)


class V11ScreeningContractTests(unittest.TestCase):
    def test_current_container_is_usable(self) -> None:
        result = validate_v11_screening_container(
            {
                "schema": 3,
                "paper": "Fixture",
                "prompt_version": V11_SCREENING_PROMPT_VERSION,
                "validator": "independent-reviewer",
                "validated_at": "2026-08-27T00:00:00Z",
                "items": {},
            },
            paper="Fixture",
        )
        self.assertTrue(result.current)
        self.assertTrue(result.usable_item_ledger)

    def test_invalid_identity_reports_all_cheap_container_errors(self) -> None:
        result = validate_v11_screening_container(
            {"schema": 2, "paper": "Other"},
            paper="Fixture",
        )
        self.assertFalse(result.current)
        self.assertFalse(result.usable_item_ledger)
        self.assertEqual(
            result.errors,
            (
                "v11 screening has an unsupported schema or paper identity",
                "v11 screening does not declare the required raw-source prompt version",
                "v11 screening lacks reviewer and validation-time metadata",
                "v11 screening has no item ledger",
            ),
        )


if __name__ == "__main__":
    unittest.main()
