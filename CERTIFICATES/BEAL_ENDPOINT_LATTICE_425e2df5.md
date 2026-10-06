# BEAL ENDPOINT LATTICE CERTIFICATE

Status: FORMALIZED_PENDING_KERNEL
Head: `425e2df5086a8a44f50617686aecd008f68ce914`

## Free lattice

Before idempotent collapse, endpoint multiplicities are represented by
`EndpointMultiset(openCount, closedCount)`, so states such as

- OPEN
- CLOSED
- OPEN + OPEN
- CLOSED + CLOSED
- OPEN + OPEN + CLOSED
- OPEN + CLOSED + CLOSED
- OPEN + OPEN + CLOSED + CLOSED

remain distinct by multiplicity.

## Idempotent quotient

After quotienting by endpoint presence, exactly four canonical states remain:

- EMPTY
- OPEN
- CLOSED
- FULL

with:

- OPEN ∨ OPEN = OPEN
- CLOSED ∨ CLOSED = CLOSED
- OPEN ∨ CLOSED = FULL
- FULL ∨ X = FULL

## Maximal state

The material FULL state is defined as `DualEndpointState`, so both endpoint
positions coexist simultaneously.

Thus:

FULL
= DUAL_ENDPOINT_STATE
= MATH
= FINAL_ROOT
= GLOBAL_EXTERNAL_CERTIFICATE

as views of the same maximal material state.

Exact strength remains:

`Nonempty FULL ↔ Nonempty Endpoint`.

- FREE_MULTIPLICITY_LATTICE: FORMALIZED
- IDEMPOTENT_FOUR_STATE_QUOTIENT: FORMALIZED
- FULL_MAXIMAL: FORMALIZED
- DUAL_ENDPOINT_COEXISTENCE: REQUIRED
- MATERIAL_ENDPOINT: SAME TERMINAL OBLIGATION
