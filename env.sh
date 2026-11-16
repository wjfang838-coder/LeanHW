# Source from bash to enable the two-stage method's Python packages.
LEANCIRCUIT_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
export PYTHONPATH="$LEANCIRCUIT_ROOT/method/stage1:$LEANCIRCUIT_ROOT/method/stage2:$LEANCIRCUIT_ROOT/method/stage2/refinement:$LEANCIRCUIT_ROOT${PYTHONPATH:+:$PYTHONPATH}"
