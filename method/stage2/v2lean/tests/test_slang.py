"""Independent direct-AST frontend tests against actual four-state HDL simulation."""
import importlib.util
import itertools
from pathlib import Path
import shutil
import tempfile
import unittest

from v2lean.fourstate_case import run_case
from v2lean.fourstate_encoding import compare_case
from v2lean.slang import SlangImporter, audit_source_proofs
from v2lean.pipeline import ROOT, run

AVAILABLE = importlib.util.find_spec('pyslang') is not None


@unittest.skipUnless(AVAILABLE, 'optional pyslang dependency')
class SlangTests(unittest.TestCase):
    @unittest.skipUnless(all(shutil.which(n) for n in ('lake', 'iverilog', 'vvp')), 'requires Lean/HDL tools')
    def test_exhaustive_operator_values(self):
        vectors = [dict(a=a+b, b=c+d, s=s) for a,b,c,d,s in itertools.product('01xz',repeat=5)]
        with tempfile.TemporaryDirectory(prefix='slang-ops-') as temp:
            result = run_case(Path(__file__).parent/'fixtures/fourstate_ops.v', 'fourstate_ops',
                              Path(temp)/'case', vectors=vectors, frontend='slang')
            self.assertEqual(result['status'], 'simulation_pass')
            self.assertEqual(result['samples'], 1024)
            self.assertEqual(result['failures'], [])
            if shutil.which('yosys'):
                encoded = compare_case(Path(temp)/'case', Path(temp)/'encoded', gold_frontend='slang')
                self.assertEqual(encoded['status'], 'encoded_diagnostic_pass')
                self.assertEqual(encoded['frontends'], {'gold': 'slang', 'gate': 'yosys'})

    @unittest.skipUnless(all(shutil.which(n) for n in ('lake', 'iverilog', 'vvp')), 'requires Lean/HDL tools')
    def test_exhaustive_signed_and_procedural_control(self):
        vectors = [dict(a=a+b, b=c+d+e, s=s) for a,b,c,d,e,s in itertools.product('01xz',repeat=6)]
        with tempfile.TemporaryDirectory(prefix='slang-control-') as temp:
            result = run_case(Path(__file__).parent/'fixtures/slang_control.v', 'slang_control',
                              Path(temp)/'case', vectors=vectors, frontend='slang')
            self.assertEqual(result['status'], 'simulation_pass', result['failures'][:2])
            self.assertEqual(result['samples'], 4096)

    def test_rejects_unmodeled_semantics(self):
        cases = [
            ('module m(input a, output tri0 y); assign y=a; endmodule', 'net type'),
            ('module m(input a, output y); wire #2 t=a; assign y=t; endmodule', 'delay/strength'),
            ('module m(input a, output y); assign (weak1,weak0) y=a; endmodule', 'drive strength'),
            ('module m(input a, output bit y); assign y=a; endmodule', 'two-state cast'),
            ('module m(input a,clk, output reg y); always @(posedge clk) y=a; endmodule', 'sensitivity'),
            ('module m(input a,s, output reg y); always @* if(s) y=a; endmodule', 'latch'),
            ('module m(input a, output reg y,z); always @* begin y=z; z=a; end endmodule', 'read before write'),
            ("module m(input a, output reg y); always @* casex(a) 1'bx:y=0; default:y=1; endcase endmodule", 'casez/casex'),
            ('module m(input a, output y); assign y=a; assign y=~a; endmodule', 'multiple/input drivers'),
        ]
        with tempfile.TemporaryDirectory(prefix='slang-reject-') as temp:
            p=Path(temp)/'m.v'
            for source, message in cases:
                with self.subTest(message=message):
                    p.write_text(source)
                    with self.assertRaisesRegex(ValueError, message): SlangImporter(p,'m').build()

    @unittest.skipUnless(shutil.which('lake'), 'requires Lean')
    def test_source_certificates_reject_wrong_lowering_and_dag(self):
        class WrongBranch(SlangImporter):
            def merge(self, selector, left, right, before):
                return left

        source = 'module m(input a,b,s, output reg y); always @* if(s) y=~a; else y=b; endmodule'
        with tempfile.TemporaryDirectory(prefix='slang-proof-') as temp:
            temp = Path(temp)
            p = temp/'m.v'
            p.write_text(source)
            importer = SlangImporter(p, 'm')
            correct = importer.build()
            prefix, suffix = correct.split('def source_scope', 1)
            self.assertIn('(.not (.var "a" 1))', prefix)
            broken_dag = prefix.replace('(.not (.var "a" 1))', '(.var "a" 1)', 1) + 'def source_scope' + suffix
            for name, text, valid in [('correct', correct, True),
                                      ('wrong_branch', WrongBranch(p, 'm').build(), False),
                                      ('wrong_dag', broken_dag, False)]:
                with self.subTest(name=name):
                    lean = temp/(name+'.lean')
                    lean.write_text(text)
                    result = run(['lake', 'env', 'lean', '-s', '65536', str(lean)],
                                 ROOT, temp/(name+'.log'), timeout=60, check=False)
                    if valid:
                        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
                        certificate = audit_source_proofs(result.stdout, importer.metadata)
                        self.assertEqual(certificate['status'], 'kernel_checked')
                    else:
                        self.assertNotEqual(result.returncode, 0)
                        self.assertIn('error:', result.stdout+result.stderr)


if __name__ == '__main__':
    unittest.main()
