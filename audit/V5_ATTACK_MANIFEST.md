# M-Core Beal V5 — auditable attack manifest

STATUS: SOURCE_CATALOG_ONLY / NO_MATHEMATICAL_PROMOTION
WRITE_BRANCH: audit/multistate-proof-refutation-v1
POLICY: FIX_FORWARD_ONLY

## Preserved prior chain
Historical K9/K10 and all prior GREEN/RED evidence remain untouched.

## V5 structural layer
- OmegaPoint carries payload.
- OmegaBottom carries payload.
- Surgery transports payload without adding arithmetic information.
- BealPayload transports a counterexample payload and proves payload preservation by rfl.
- Firewall marks endpoint assumptions circular.
- No V5 definition asserts BealConjecture or CommonPrime.

## Exact frontier
ArithmeticResidue := forall d : BealData, BealCounterexample d -> False

This is deliberately a Prop definition. V5 does NOT prove it.

## Certification policy
GREEN may be issued only after targeted build, #print axioms, incomplete-proof scan and negative control.
ArithmeticResidue remains OPEN_BRIDGE until a genuine proof exists.
Mechanical CI success never implies mathematical closure.
