# BEAL External Reuse Ledger — 2026-09-26

Status: FAIL-CLOSED
Purpose: reuse public formal mathematics without weakening existing GREEN/FROZEN/CERTIFIED gates.

## Rule

External material is classified in exactly one of these states:

- `CODE_REUSE_ALLOWED`: repository license explicitly verified compatible with reuse.
- `CITATION_ONLY`: public source may be cited as mathematical/computational provenance, but no code is copied into the Lean proof tree.
- `NOT_A_CLOSURE`: source is relevant but does not prove the Beal terminal obligation.

No external source may promote `BealUnconditionalKernelObligation`,
`BealUnconditionalClaimCertificate`, `BealProofCertificate`, or
`BealConjecture` unless a kernel-checked adapter proves the exact local proposition.

## Exact terminal target

```lean
abbrev BealUnconditionalKernelObligation : Prop :=
  ¬ T34FreyNodalCollisionCandidate
```

Equivalent terminal objects already frozen in this repository:

```text
¬ T34FreyNodalCollisionCandidate
  -> BealUnconditionalClaimCertificate
  -> BealProofCertificate
  -> BealConjecture
```

## CODE_REUSE_ALLOWED

### leanprover-community/mathlib4

- License: Apache-2.0 (verified via GitHub repository metadata).
- Role: foundational algebra/number theory/elliptic-curve infrastructure.
- Current local use: isolated B01 gate already uses Mathlib v4.30-compatible APIs.
- Promotion rule: ordinary Lean kernel check + local axiom audit.
- Closure status: `NOT_A_CLOSURE` for Beal by itself.

### ImperialCollegeLondon/FLT

- License: Apache-2.0 (verified via repository LICENSE/GitHub metadata).
- Role: Lean formalization infrastructure for the modular method, Frey curves,
  Galois representations, deformation theory and level-lowering.
- Reuse mode: port/adapt only through a dedicated compatibility branch; do not
  change the canonical m-core-beal toolchain merely to import it.
- Closure status: `NOT_A_CLOSURE` for mixed-exponent Beal families.

### anthropics/fermats-last-theorem

- License: Apache-2.0 (verified via repository LICENSE/GitHub metadata).
- Lean: v4.33.1; Mathlib pinned to its own revision.
- Verified artifact reports `sorry_count = 0` and final theorem axioms
  `[propext, Classical.choice, Quot.sound]`.
- Particularly relevant proved components:
  - Frey-package construction;
  - Frey representation irreducibility in the FLT setting;
  - semistable modularity;
  - Ribet-style level lowering in the exact FLT setting;
  - vanishing of weight-2 cusp forms at level 2.
- Reuse mode: source-port selected generic lemmas only after statement audit.
  Direct dependency injection into the existing v4.30 gate is prohibited.
- Closure status: `NOT_A_CLOSURE`; its theorem is equal-exponent FLT, not Beal.

## CITATION_ONLY

The following repositories are public and mathematically relevant but GitHub
metadata exposes no repository license as of this audit. They may therefore be
cited, but their code must not be copied into m-core-beal without a separately
verified license grant.

### akoutsianas/pp5

Electronic resources for the generalized Fermat equation
`x^p + y^p = z^5`. Relevant provenance includes conductor calculations,
potential multiplicative reduction, irreducibility, and newform elimination.
Useful for B01/B02 methodology and test vectors. `CITATION_ONLY`.

### NicolasBillerey/xhyper

Electronic resources for Darmon's program for generalized Fermat equations,
including signatures `(11,11,p)` and `(7,7,p)`, with Frey curves,
irreducibility and elimination computations. `CITATION_ONLY`.

### michaud-jacobs/thesis

Magma code supporting work on level lowering, Hilbert newforms, generalized
Fermat equations and newform elimination. `CITATION_ONLY`.

### isomorphic-ai/fermat

Lean fixed-exponent Fermat developments with multiple kernel-checked endpoints.
GitHub metadata currently exposes no repository license, so this audit treats it
as `CITATION_ONLY` despite its technical relevance.

## Mapping to local OPEN_MATH

| Local target | Safe external support | Status after reuse |
| --- | --- | --- |
| B01 local elliptic/Frey infrastructure | Mathlib + FLT projects | reusable infrastructure only |
| B01 modularity/level-lowering interfaces | Anthropic FLT / Imperial FLT | reusable after statement/toolchain port |
| T53 (4,4,p) elimination | generalized-Fermat literature/computation | still OPEN_MATH unless exact proof is formalized |
| T54 (4,p,p) elimination | generalized-Fermat literature/computation | still OPEN_MATH unless exact proof is formalized |
| T55 (4,p,q) elimination | generalized-Fermat literature/computation | still OPEN_MATH unless exact proof is formalized |
| T56 (p,p,q) elimination | generalized-Fermat literature/computation | still OPEN_MATH unless exact proof is formalized |
| T57 (p,q,r) elimination | generalized-Fermat literature/computation | still OPEN_MATH unless exact proof is formalized |
| `¬ T34FreyNodalCollisionCandidate` | no verified public Beal proof found | OPEN_MATH_CORE |

## Non-negotiable promotion rule

A citation, paper, Magma transcript, external theorem name, or successful
computation is not itself a Lean inhabitant.

Promotion to `THEOREM_ENABLED` requires one of:

1. a kernel-checked proof of `BealUnconditionalKernelObligation`; or
2. a kernel-checked inhabitant of `BealUnconditionalClaimCertificate`; or
3. an explicit verified Beal counterexample on the refutation lane.

Until then the theorem remains fail-closed.
