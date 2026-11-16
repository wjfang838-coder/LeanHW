from pathlib import Path
import sys
stage1 = Path(__file__).resolve().parents[2]
if str(stage1) not in sys.path:
    sys.path.insert(0, str(stage1))
