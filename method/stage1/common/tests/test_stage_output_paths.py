from types import SimpleNamespace
from common import paths
from leanspec import pipeline


def test_stage1_global_ledger_belongs_to_data_not_method(tmp_path):
    case = SimpleNamespace(dir=str(tmp_path), name='fixture')
    assert pipeline._chain(case).root == paths.DATA
