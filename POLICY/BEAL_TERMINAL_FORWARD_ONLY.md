# BEAL TERMINAL FORWARD-ONLY POLICY

The Beal OPEN_MATH search is truncated at `FinalMixedExclusion`.

Rules:

- Do not reopen previously kernel-checked structural reductions.
- Do not introduce equivalent hypotheses as new OPEN_MATH leaves.
- Do not introduce renamed endpoint assumptions.
- Do not promote a terminal leaf merely because downstream implications are already proved.
- Any future closure commit must construct `FinalMixedExclusion` materially.
- Once that producer compiles and passes the axiom audit, the existing endpoint bridge is sufficient for promotion.

This policy is an orchestration freeze, not a mathematical proof of the terminal proposition.
