"""Certificate rejection must survive Python's -O and -OO options."""
import ast
from pathlib import Path
import subprocess
import sys
import unittest

HERE = Path(__file__).resolve().parent


class OptimizationSafety(unittest.TestCase):
    def test_no_removable_assertions(self):
        for path in HERE.rglob('*.py'):
            with self.subTest(file=str(path.relative_to(HERE))):
                self.assertFalse(any(isinstance(node, ast.Assert)
                                     for node in ast.walk(ast.parse(path.read_text()))))

    def test_corrupt_certificates_rejected_under_optimization(self):
        code = '''
import sys
from pathlib import Path
root = Path(sys.argv[1])
sys.path[:0] = [str(root/'independent-merge-filter'), str(root/'model_audit')]
from merge_check import check_points
from snub_check import check as primary
from snub_check_rational import check as independent, I

square = [((x, 0, 0, 0), (y, 0, 0, 0))
          for x, y in [(0, 0), (1, 0), (1, 1), (0, 1)]]
if check_points(square, square, [1, 2, 3, 0]) != 6:
    raise RuntimeError('valid exact congruence rejected')
controls = [
    ('non-bijection', lambda: check_points(square, square, [0, 0, 2, 3])),
    ('wrong distance', lambda: check_points(square, square, [0, 2, 1, 3])),
    ('primary schema', lambda: primary({'schema': -1})),
    ('independent schema', lambda: independent({'schema': -1})),
    ('reversed interval', lambda: I(2, 1)),
    ('zero divisor', lambda: I(1)/I(-1, 1)),
]
for name, check in controls:
    try:
        check()
    except AssertionError:
        pass
    else:
        raise RuntimeError('corruption accepted: '+name)
print('PASS six explicit certificate rejections')
'''
        for option in ('-O', '-OO'):
            with self.subTest(option=option):
                result = subprocess.run([sys.executable, option, '-c', code, str(HERE)],
                                        capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn('PASS six explicit certificate rejections', result.stdout)


if __name__ == '__main__':
    unittest.main()
