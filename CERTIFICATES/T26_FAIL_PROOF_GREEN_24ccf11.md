# T26 FAIL-PROOF Certificate

Status: **GREEN / FAIL-CLOSED**

This certificate does **not** prove or refute the Beal conjecture.
It certifies that the specific inference strategy audited here — promoting the
already-certified 38970a1 result through the current Frey discriminant /
2-adic chain — still requires a bridge equivalent to the Beal endpoint itself.

## Frozen scientific SHA

`24ccf11b75560cc6bc09828b9f61f2d02e3f0240`

Frozen branch:

`frozen/t26-fail-proof-green-24ccf11`

Parent T25:

`80ca07f854c2522cb30a6f6ccc09ecb4259cc038`

Parent T24:

`e01b67c3c77489f30b6357f4c0a22fb214af9bb1`

## CI evidence

Workflow: `certificate`

Run: `35519312085`

Job: `106100523185`

Conclusion: **SUCCESS**

All gates G0-G6 passed, including:

- fail-closed source hygiene;
- frozen K9 regression;
- K10 prime-divisor closure;
- theorem-specific foundation audit;
- endpoint remains non-promoted;
- backward oracle A/B test;
- clean reproduction via `lake clean && lake build MCore`.

## T26 formal result

The external 38970a1 certificate is granted as an inhabited logical token:

`MCore.T26Base38970Certified`

The remaining Frey contradiction bridge is:

`MCore.T26FreyContradictionBridge`

The proposed cross-domain bridge is:

`MCore.T26CertifiedBaseToFreyBridge`

Central theorem:

```text
MCore.T26_beal_iff_certified_base_frey_bridge :
  BealConjecture ↔ T26CertifiedBaseToFreyBridge
```

Therefore, after granting the 38970a1 certificate and all T24-T25 Frey facts,
the missing implication is still equivalent to the original Beal endpoint.
The current logic has not reduced the open mathematical residual.

## Axiom audit

From run `35519312085`:

```text
'MCore.T26_base_38970_certified' does not depend on any axioms
'MCore.T26_frey_bridge_iff_T25_frontier' does not depend on any axioms
'MCore.T26_certified_base_bridge_iff_frey_bridge' does not depend on any axioms
'MCore.T26_beal_iff_certified_base_frey_bridge' depends on axioms: [propext, Quot.sound]
'MCore.T26_unrestricted_cross_domain_promotion_refuted' does not depend on any axioms
```

No `sorry`, `admit`, project axiom, or `Classical.choice` was introduced.

## Invalid transfer rule explicitly rejected

T26 also proves:

```text
¬ T26UnrestrictedCrossDomainPromotion
```

where the rejected schema is:

```text
∀ P Q : Prop, P → Q
```

This is the formal sanity check against treating a proved positive invariant in
one mathematical object/domain as sufficient, by itself, to prove an unrelated
target proposition in another domain.

## Scientific boundary

Certified:

- T24 exact Frey discriminant rewrite;
- T25 exact 2-adic factor transport into the Frey discriminant;
- T26 logical bridge audit and fail-closed equivalence.

Not certified:

- semistability of the full generalized Beal Frey family;
- exact conductor formula for all admissible tuples;
- level lowering sufficient to eliminate all primitive candidates;
- a contradiction from the 38970a1 regulator bound;
- `BealConjecture`.

Final status:

```text
T26_FAIL_PROOF = CERTIFIED
BEAL_ENDPOINT = OPEN_BRIDGE
PROMOTION = REFUSED
SCIENTIFIC_CLAIM_PROVED = false
```

Interpretation of "FAIL-PROOF": the audited proof strategy fails closed at a
precisely identified bridge. It is **not** a proof that Beal is false and is
**not** a proof that no future argument can close the bridge.
