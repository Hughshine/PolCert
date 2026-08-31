#!/usr/bin/env python3
from __future__ import annotations

import pathlib
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from io import StringIO

import check_open_proofs


class OpenProofScannerTests(unittest.TestCase):
    def scan(self, text: str) -> list[tuple[int, str]]:
        with tempfile.TemporaryDirectory(prefix="polcert-open-proof-") as tmp:
            path = pathlib.Path(tmp) / "Fixture.v"
            path.write_text(text, encoding="utf-8")
            return check_open_proofs.find_open_proofs(path)

    def test_rejects_unfinished_commands(self) -> None:
        self.assertEqual(
            self.scan("Goal True.\n  admit.\nAdmitted.\nGoal True. Abort.\n"),
            [(2, "admit"), (3, "Admitted"), (4, "Abort.")],
        )

    def test_ignores_comments_strings_and_identifiers(self) -> None:
        source = '''
(** Admitted. (* nested admit *) *)
Definition message := "Abort. and Admitted.".
Definition Admitted_helper := true.
Goal True. exact I. Qed.
'''
        self.assertEqual(self.scan(source), [])

    def test_preserves_line_numbers_across_nested_comments(self) -> None:
        source = "(* outer\n(* inner *)\n*)\nGoal True.\nAdmitted.\n"
        self.assertEqual(self.scan(source), [(5, "Admitted")])

    def test_gate_exit_statuses(self) -> None:
        with tempfile.TemporaryDirectory(prefix="polcert-open-proof-gate-") as tmp:
            root = pathlib.Path(tmp)
            clean = root / "Clean.v"
            dirty = root / "Dirty.v"
            clean.write_text("Goal True. exact I. Qed.\n", encoding="utf-8")
            dirty.write_text("Goal True. Admitted.\n", encoding="utf-8")
            stdout = StringIO()
            stderr = StringIO()
            with redirect_stdout(stdout), redirect_stderr(stderr):
                self.assertEqual(check_open_proofs.check_files([clean]), 0)
                self.assertEqual(check_open_proofs.check_files([dirty]), 1)
                self.assertEqual(
                    check_open_proofs.check_files([root / "Missing.v"]), 2
                )
            self.assertIn("expected=0 actual=0", stdout.getvalue())
            self.assertIn("expected=0 actual=1", stderr.getvalue())
            self.assertIn("ERROR missing=", stderr.getvalue())


if __name__ == "__main__":
    unittest.main()
