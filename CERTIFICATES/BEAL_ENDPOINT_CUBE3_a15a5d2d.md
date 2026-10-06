# BEAL ORDERED ENDPOINT CUBE ≤3 + FULL CERTIFICATE

Status: FORMALIZED_PENDING_KERNEL
Head: `a15a5d2da34b2ee5c687a45b681014e0d27b471d`

## Ordered free states

Length 1:
- OPEN
- CLOSED

Length 2:
- OPEN+CLOSED
- CLOSED+OPEN
- OPEN+OPEN
- CLOSED+CLOSED

Length 3:
- OPEN+OPEN+OPEN
- CLOSED+CLOSED+CLOSED
- OPEN+OPEN+CLOSED
- OPEN+CLOSED+OPEN
- CLOSED+OPEN+OPEN
- OPEN+CLOSED+CLOSED
- CLOSED+OPEN+CLOSED
- CLOSED+CLOSED+OPEN

Maximal published word:
- FULL = OPEN+OPEN+CLOSED+CLOSED

The ordered layer preserves word order before quotienting, so
OPEN+CLOSED and CLOSED+OPEN are distinct free states.

## Idempotent collapse

All words collapse by presence/absence of OPEN/CLOSED to the four canonical
states EMPTY / OPEN / CLOSED / FULL.

FULL collapses to the maximal canonical state and its material interpretation
is the existing DualEndpointState, hence the published
GLOBAL_EXTERNAL_CERTIFICATE view.

- ORDERED_STATES_1_TO_3: 14/14 FORMALIZED
- PREVIOUSLY_MISSING_STATES: 10/10 FORMALIZED
- FULL_WORD: FORMALIZED
- IDEMPOTENT_COLLAPSE: FORMALIZED
- MATERIAL_FULL: DUAL_ENDPOINT_STATE
