#!/usr/bin/env python3
"""ISS bridge lexer regressions, including identifiers emitted by PolCert."""
import contextlib
import io
from pathlib import Path
import re
import tempfile
import unittest

from pluto_iss_check import (Constraint, Program, Stmt, collect_var_order,
                            constraint_to_domain_rows, main, parse_affine,
                            parse_program, collect_iss_structure)


class IssLexerTests(unittest.TestCase):
    def test_wire_order_names_all_high_dimensional_coefficients(self):
        names = ['$i' + str(i) for i in range(11)]
        constraint = Constraint('ge', tuple((name, i + 1) for i, name in enumerate(names)), 3)
        stmt = Stmt(1, 'A=0;', 11, 11, [constraint], '', [], [], [True] * 11)
        program = Program(11, 2, ['Z', 'A'], [stmt], [])
        order = collect_var_order(program, program, {})
        self.assertEqual(order[:2], ['Z', 'A'])
        self.assertLess(order.index('$i10'), order.index('$i2'))
        row = constraint_to_domain_rows(constraint, order)[0]
        self.assertEqual(dict(zip(order, row['coeffs'])),
                         {'Z': 0, 'A': 0, **{name: -(i + 1) for i, name in enumerate(names)}})

    def test_wire_basis_cannot_discard_names(self):
        constraint = Constraint('ge', (('$i10', 1),), 0)
        for order in (['$i2'], ['$i10', '$i10']):
            with self.subTest(order=order), self.assertRaises(ValueError):
                constraint_to_domain_rows(constraint, order)

    def test_parameter_contract(self):
        before = Program(0, 2, ['N', 'M'], [], [])
        for after in (Program(0, 2, ['M', 'N'], [], []),
                      Program(0, 2, ['N'], [], [])):
            with self.subTest(after=after), self.assertRaises(ValueError):
                collect_iss_structure(before, after)
        duplicate = Program(0, 2, ['N', 'N'], [], [])
        with self.assertRaises(ValueError):
            collect_var_order(duplicate, duplicate, {})

    def test_generated_identifier(self):
        self.assertEqual(parse_affine('-2$i0+N-1'), ((('$i0', -2), ('N', 1)), -1))
        self.assertEqual(parse_affine('2$i0-N'), ((('$i0', 2), ('N', -1)), 0))

    def test_existing_identifiers(self):
        self.assertEqual(parse_affine("2i'-N+1"), ((('N', -1), ("i'", 2)), 1))

    def test_constants_and_cancellation(self):
        self.assertEqual(parse_affine('$i0-$i0+2-7'), ((), -5))
        self.assertEqual(parse_affine('0'), ((), 0))
        self.assertEqual(parse_affine(''), ((), 0))

    def test_unknown_syntax_fails_closed(self):
        for expression in ('i+@j', '2*i', 'i/N', 'i--j', 'i+', '+'):
            with self.subTest(expression=expression), self.assertRaises(ValueError):
                parse_affine(expression)

    def test_generated_names_preserve_complete_split(self):
        data = Path(__file__).resolve().parents[2] / 'tests/iss-pluto-dumps'
        before = (data / 'reverse_before.txt').read_text()
        after = (data / 'reverse_after.txt').read_text()
        for source, target in [('i', '$i0'), ('N', 'N')]:
            before = re.sub(r'\b' + source + r'\b', lambda _: target, before)
            after = re.sub(r'\b' + source + r'\b', lambda _: target, after)
        _, payload = collect_iss_structure(parse_program(before), parse_program(after))
        self.assertIn('bridge', payload)

    def test_historical_dump_compatibility(self):
        data = Path(__file__).resolve().parents[2] / 'tests/iss-pluto-dumps'
        for name in ('reverse', 'heat_2dp', 'jacobi_2d_periodic', 'multi_stmt_periodic'):
            with self.subTest(kernel=name):
                before = (data / (name + '_before.txt')).read_text()
                after = (data / (name + '_after.txt')).read_text()
                _, payload = collect_iss_structure(parse_program(before), parse_program(after))
                self.assertIn('bridge', payload)

    def test_combined_dump_with_undecodable_debug_bytes(self):
        # Pluto's --moredebug output can print uninitialized multiplier names
        # (observed on jacobi-3d-periodic). The bridge must still be recovered.
        data = Path(__file__).resolve().parents[2] / 'tests/iss-pluto-dumps'
        before = (data / 'reverse_before.txt').read_bytes()
        after = (data / 'reverse_after.txt').read_bytes()
        noise = b'[pluto] eliminating multiplier 0 (c_\x83) from 30 constraints\n'
        with tempfile.TemporaryDirectory() as directory:
            combined = Path(directory) / 'combined.txt'
            combined.write_bytes(noise + before + after)
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                code = main(['pluto_iss_check.py', '--emit-bridge-from-combined', str(combined)])
        self.assertEqual(code, 0, output.getvalue())
        self.assertIn('AFTER_STMTS', output.getvalue())


if __name__ == '__main__':
    unittest.main()
