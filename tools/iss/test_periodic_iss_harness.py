"""Check that periodic adaptation evidence detects wrong reads and executions."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'tools/end_to_end_c'))
from loop_to_c import INTEGER_HELPERS_C,transpile_loop_text
from run_periodic_iss_suite import harness,harness_2d,phase_harness


class PeriodicHarnessTests(unittest.TestCase):
    def check(self,source,optimized,rank=1):
        selected=harness_2d if rank==2 else harness
        code,_,_=selected(source,optimized,transpile_loop_text,INTEGER_HELPERS_C)
        with tempfile.TemporaryDirectory(prefix='periodic-iss-check-') as temporary:
            directory=Path(temporary);(directory/'check.c').write_text(code)
            build=subprocess.run(['cc','-O0','-std=c99',str(directory/'check.c'),'-o',str(directory/'check')],capture_output=True,text=True)
            self.assertEqual(build.returncode,0,build.stderr)
            return subprocess.run([str(directory/'check')],capture_output=True,text=True).returncode

    def setUp(self):
        self.source=(ROOT/'tests/iss-native/jacobi_1d_periodic_phase.loop').read_text()

    def test_faithful_phase_and_guards(self):
        for name in ['phase','guards','quotient']:
            candidate=(ROOT/('tests/iss-native/jacobi_1d_periodic_'+name+'.loop')).read_text()
            with self.subTest(name=name):self.assertEqual(self.check(self.source,candidate),0)

    def test_wrong_buffer_rejected(self):
        self.assertNotEqual(self.check(self.source,self.source.replace('u[p]','u[(1-p)]')),0)

    def test_wrong_wraparound_rejected(self):
        self.assertNotEqual(self.check(self.source,self.source.replace('u[p][(N - 1)]','u[p][0]')),0)

    def test_missing_update_rejected(self):
        self.assertNotEqual(self.check(self.source,self.source.replace('range(0, N)','range(0, (N - 1))')),0)

    def test_duplicate_execution_rejected(self):
        self.assertNotEqual(self.check(self.source,self.source+self.source),0)

    def test_2d_faithful_phase(self):
        source=(ROOT/'tests/iss-native/jacobi_2d_periodic_phase.loop').read_text()
        self.assertEqual(self.check(source,source,2),0)

    def test_2d_wrong_diagonal_rejected(self):
        source=(ROOT/'tests/iss-native/jacobi_2d_periodic_phase.loop').read_text()
        wrong=source.replace('u[p][(N - 1)][(N - 1)]','u[p][(N - 1)][0]')
        self.assertNotEqual(self.check(source,wrong,2),0)


PHASE_SPLIT='''context(T, N);

for q in range(0, T) {
  if ((2 * q + 1) <= (T - 1)) {
    for i in range(0, N) {
      u[1][i] = ((i == 0) ? u[0][(N - 1)] : u[0][(i - 1)]) + u[0][i] + ((i == (N - 1)) ? u[0][0] : u[0][(i + 1)]);
    }
  }
  if ((2 * q + 2) <= (T - 1)) {
    for i in range(0, N) {
      u[0][i] = ((i == 0) ? u[1][(N - 1)] : u[1][(i - 1)]) + u[1][i] + ((i == (N - 1)) ? u[1][0] : u[1][(i + 1)]);
    }
  }
}
'''


class PhaseHarnessTests(unittest.TestCase):
    """The evaluation's generic phase-form observer for periodic ISS rows."""
    def run_check(self,optimized):
        source=(ROOT/'tests/iss-native/jacobi_1d_periodic_phase.loop').read_text()
        code,_,samples=phase_harness(source,optimized,transpile_loop_text,INTEGER_HELPERS_C)
        with tempfile.TemporaryDirectory(prefix='phase-iss-check-') as temporary:
            directory=Path(temporary);(directory/'check.c').write_text(code)
            build=subprocess.run(['cc','-O0','-std=gnu11',str(directory/'check.c'),'-o',str(directory/'check')],capture_output=True,text=True)
            self.assertEqual(build.returncode,0,build.stderr)
            run=subprocess.run([str(directory/'check')],capture_output=True,text=True)
            return run.returncode,len(run.stdout.splitlines()),samples

    def test_phase_split_accepted(self):
        code,lines,samples=self.run_check(PHASE_SPLIT)
        self.assertEqual((code,lines),(0,samples))

    def test_unsplit_candidate_rejected(self):
        source=(ROOT/'tests/iss-native/jacobi_1d_periodic_phase.loop').read_text()
        with self.assertRaises(ValueError):phase_harness(source,source,transpile_loop_text,INTEGER_HELPERS_C)

    def test_missing_phase_rejected(self):
        missing=PHASE_SPLIT.replace('(2 * q + 2) <= (T - 1)','(2 * q + 2) <= (T - 3)')
        self.assertNotEqual(self.run_check(missing)[0],0)

    def test_wrong_buffer_rejected(self):
        self.assertNotEqual(self.run_check(PHASE_SPLIT.replace('u[1][i] =','u[0][i] ='))[0],0)

    def test_wrong_wraparound_rejected(self):
        self.assertNotEqual(self.run_check(PHASE_SPLIT.replace('u[0][(N - 1)] :','u[0][0] :'))[0],0)


if __name__=='__main__':unittest.main()
