# V22 GREEN checkpoint — Beal × M-Core residual architecture

PROOF_HEAD: 636156c2a2802bf48f67c3391cba0179ed2a4293
SCIENTIFIC_MODULE_COMMIT: 01e1b294b016247b64902b89aa9034318d526bee
RUN: 35483782906
JOB: 106006245525
TARGET: k10 / MCore library validation
STATUS: SUCCESS
ARTIFACT_HASH: absent

V22 establishes the exact wiring:
BealConjecture ↔ PrimitiveObstruction ↔ absence of normalized/primitive counterexample candidates.
It marks BEAL-PRIMITIVE-OBSTRUCTION OPEN_EXACT and does not claim the conjecture.

Naming rule: new mathematical stages after legacy K checkpoints use V only.

Crossing rule: START→CENTER and END→CENTER must record the first formally verified shared object as CROSSING_NODE, including hypotheses, quantifiers, directionality, residual-before/after, axiom audit, and circularity audit. A gap is OPEN_EXACT, not closure.

M-Core detection rule: when a residual/crossing instantiates an M-Core structure, report M-CORE STRUCTURE DETECTED; if the crossing itself does, report M-CORE CROSSING DETECTED.
