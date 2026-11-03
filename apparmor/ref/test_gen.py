import tempfile
import unittest
from unittest.mock import patch
from types import SimpleNamespace

import gen


class GeneratorTests(unittest.TestCase):
    def test_seed_policy_keeps_denial_and_adds_allow(self):
        r = gen.Rng(2026)
        gen.random.seed(2026)
        for i in range(9):
            pol = gen.gen_policy(r, i)
            names = ['main', 'main//c1', 'other'] + (
                ['main//h1'] if any(c.hat for c in pol['profiles'][0].children) else [])
            gen.gen_queries(r, pol, names)
        rules = pol['profiles'][1].rules
        self.assertTrue(any(x.kind == 'file' and x.q['audit'] and x.q['deny'] for x in rules))
        self.assertTrue(any(x.kind == 'file' and not x.q['deny'] for x in rules))

    def test_parser_diagnostics_include_signal_and_all_output(self):
        result = SimpleNamespace(returncode=-11, stdout='first\nsecond\n', stderr='one\ntwo\n')
        with tempfile.TemporaryDirectory() as tmp, patch('gen.subprocess.run', return_value=result):
            ok, message = gen.parser_accepts({'main': ''}, 'main', tmp)
        self.assertFalse(ok)
        self.assertIn('signal 11', message)
        self.assertIn('first\nsecond\n', message)
        self.assertIn('one\ntwo\n', message)


if __name__ == '__main__':
    unittest.main()
