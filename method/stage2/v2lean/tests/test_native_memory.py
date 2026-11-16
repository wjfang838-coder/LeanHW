import copy
import unittest

from v2lean.importer import Unsupported
from v2lean.memorycheck import write_orders, rejected_write_pairs
from v2lean.memblock_compat import describe, cut_memories


def memory_module():
    widths = {'RD_ADDR': 1, 'RD_ARST': 1, 'RD_CLK': 1, 'RD_DATA': 8,
              'RD_EN': 1, 'RD_SRST': 1, 'WR_ADDR': 2, 'WR_CLK': 2,
              'WR_DATA': 16, 'WR_EN': 16}
    connections, next_bit = {}, 2
    for name, width in widths.items():
        connections[name] = list(range(next_bit, next_bit + width))
        next_bit += width
    connections.update(RD_EN=['1'], RD_ARST=['0'], RD_SRST=['0'], RD_CLK=['x'])
    numbers = dict(ABITS=1, WIDTH=8, SIZE=2, OFFSET=0, RD_PORTS=1, WR_PORTS=2,
                   RD_CE_OVER_SRST=0, RD_CLK_ENABLE=0, RD_CLK_POLARITY=0,
                   RD_COLLISION_X_MASK=0, RD_TRANSPARENCY_MASK=0,
                   RD_WIDE_CONTINUATION=0, WR_PRIORITY_MASK=0,
                   WR_WIDE_CONTINUATION=0, WR_CLK_ENABLE=3, WR_CLK_POLARITY=3)
    parameters = {k: format(v, '032b') for k, v in numbers.items()}
    parameters.update(MEMID='\\mem', INIT='1010010100010010',
                      RD_ARST_VALUE='x'*8, RD_SRST_VALUE='x'*8, RD_INIT_VALUE='x'*8)
    return {'ports': {}, 'netnames': {}, 'cells': {'mem': {
        'type': '$mem_v2', 'parameters': parameters, 'connections': connections,
        'port_directions': {n: 'output' if n == 'RD_DATA' else 'input' for n in widths}}}}


class NativeMemoryTests(unittest.TestCase):
    def test_write_pair_pruning_requires_an_actual_unequal_observation(self):
        mem = {'name': 'm', 'wp': 3, 'gate_write_order': [2, 0, 1]}
        trace = {'signal': [{'name': 'cmp_m_wa0', 'wave': '04'},
                            {'name': 'cmp_m_we1', 'wave': '14'},
                            {'name': 'cmp_m_wd2', 'wave': 'x4'},
                            {'name': 'cmp_other_wa2', 'wave': '04'}]}
        self.assertEqual(rejected_write_pairs(trace, [mem]), {(0, 0, 2)})
        self.assertEqual(rejected_write_pairs({'signal': []}, [mem]), set())

    def test_initialization_and_rejected_contracts(self):
        module = memory_module()
        self.assertEqual(describe(module)[0]['init_words'], [0x12, 0xa5])
        partial = copy.deepcopy(module)
        partial['cells']['mem']['parameters']['ABITS'] = format(32, '032b')
        partial['cells']['mem']['connections']['RD_ADDR'] = ['0'] * 32
        partial['cells']['mem']['connections']['WR_ADDR'] = ['0'] * 64
        self.assertEqual(describe(partial)[0]['size'], 2)
        for field, value in [('INIT', 'x' + '0'*15), ('SIZE', '11'),
                             ('WR_PRIORITY_MASK', '1'), ('WR_CLK_POLARITY', '1'),
                             ('RD_CLK_ENABLE', '1'), ('RD_TRANSPARENCY_MASK', '1')]:
            with self.subTest(field=field):
                bad = copy.deepcopy(module)
                bad['cells']['mem']['parameters'][field] = value
                with self.assertRaises(Unsupported):
                    describe(bad)

    def test_write_correspondence_is_bijective_and_complete(self):
        module = memory_module()
        memories = describe(module)
        self.assertEqual(list(write_orders(memories)), [((0, 1),), ((1, 0),)])
        with self.assertRaises(Unsupported):
            write_orders([{'wp': 7}])
        cell = module['cells'].pop('mem')
        cell['parameters']['MEMID'] = '\\' + memories[0]['name']
        module['cells']['emitted'] = cell
        memories[0]['gate_write_order'] = [1, 0]
        cut, _ = cut_memories(module, memories, emitted=True)
        name = memories[0]['name']
        self.assertEqual(cut['ports'][name + '_we0']['bits'], cell['connections']['WR_EN'][8:])
        self.assertEqual(cut['ports'][name + '_wc1']['bits'], cell['connections']['WR_CLK'][:1])
        # Every mask bit is observed, even though Lean's write enable is scalar.
        self.assertEqual(len(cut['ports'][name + '_we0']['bits']), 8)
        memories[0]['gate_write_order'] = [0, 0]
        with self.assertRaises(Unsupported):
            cut_memories(module, memories, emitted=True)


if __name__ == '__main__':
    unittest.main()
