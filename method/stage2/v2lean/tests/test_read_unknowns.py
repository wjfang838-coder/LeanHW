import copy
import unittest

from v2lean.importer import Unsupported
from v2lean.read_unknowns import read_origins


class ReadOriginTests(unittest.TestCase):
    def setUp(self):
        self.mem = {'name': 'v2lean_memory_0', 'source_memid': '\\mem', 'rp': 2, 'dw': 2}
        self.module = {
            'cells': {'mem': {'type': '$mem_v2', 'parameters': {'MEMID': '\\mem'},
                              'connections': {'RD_DATA': [2, 3, 4, 5]}}},
            'netnames': {
                '$memrd$\\mem$original.v:10$2_DATA': {
                    'bits': [2, 3], 'attributes': {'src': 'original.v:10.4-10.7'}},
                '$memrd$\\mem$original.v:20$3_DATA': {
                    'bits': [4, 5], 'attributes': {'src': 'original.v:20.4-20.7'}}}}

    def test_read_port_order_comes_from_physical_data_bus(self):
        self.assertEqual([o['line'] for o in read_origins(self.module, self.mem)], [10, 20])
        self.module['cells']['mem']['connections']['RD_DATA'] = [4, 5, 2, 3]
        self.assertEqual([o['line'] for o in read_origins(self.module, self.mem)], [20, 10])

    def test_missing_ambiguous_or_inconsistent_origin_is_rejected(self):
        for alteration in ('missing', 'ambiguous', 'source_mismatch', 'shared_location'):
            with self.subTest(alteration=alteration):
                module = copy.deepcopy(self.module)
                nets = module['netnames']
                key = '$memrd$\\mem$original.v:10$2_DATA'
                if alteration == 'missing':
                    nets[key]['bits'] = [2, 9]
                elif alteration == 'ambiguous':
                    nets['$memrd$\\mem$original.v:10$99_DATA'] = copy.deepcopy(nets[key])
                elif alteration == 'source_mismatch':
                    nets[key]['attributes']['src'] = 'original.v:11.4-11.7'
                else:
                    net = nets.pop('$memrd$\\mem$original.v:20$3_DATA')
                    net['attributes']['src'] = 'original.v:10.9-10.12'
                    nets['$memrd$\\mem$original.v:10$3_DATA'] = net
                with self.assertRaises(Unsupported):
                    read_origins(module, self.mem)


if __name__ == '__main__':
    unittest.main()
