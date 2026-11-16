---
id: dev-tb-not-oracle
layer: process
applies_to: CVDP-agentic authoring (scored config)
principle: spec-is-the-oracle
lib: docs/instructions/CORE.md §5 (agentic addendum)
maturity: promoted
strike: 2
---
# The dev testbench is not the oracle

The scored configuration is the spec's DEFAULT parameters (the hidden `test_runner` binds env-default `-P` values = the docs' declared defaults), NOT the dev testbench's instantiation. Authoring to a dev-TB's registered 3-input version fails scoring when the env-default is a combinational 4-input (multiplexer_0001, strike 1; signed_comparator/queue/direct_map, strike 2). Two facets: (1) config comes from documented defaults, not dev-TB overrides; (2) the dev-TB's same-edge drive+sample delta-cycle race can make a structural DUT look like it wants negedge — trust the spec + hidden scorer, do not flip edges on dev-TB evidence (universal_shift_reg / cont_adder). If a derived localparam is documented (`$clog2` INDEX_WIDTH), the scorer probes it by name — emit it verbatim.
