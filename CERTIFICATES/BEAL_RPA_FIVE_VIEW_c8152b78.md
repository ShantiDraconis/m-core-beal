# BEAL RPA FIVE-VIEW CERTIFICATE

Status: FORMALIZED_PENDING_KERNEL
Head: `c8152b7845216453150fbe8b378b98888d1367bc`

## RPA duality

The certificate keeps both sides of the transition simultaneously:

- OPEN_MATH witness
- CLOSED_MATH witness
- forward map OPEN -> CLOSED
- backward map CLOSED -> OPEN
- identity preservation in both directions

The terminal identity is exposed in five views:

OPEN/CLOSED transition
= OPEN_BRIDGE/CLOSED_BRIDGE transition
= MATH
= FINAL_ROOT
= GLOBAL_EXTERNAL_CERTIFICATE.

## Exact logical strength

`Nonempty RPADualConfirmation ↔ Nonempty Endpoint`.

Therefore the RPA certificate is exactly as strong as the terminal
mathematical inhabitant. It neither loses nor manufactures the endpoint.

- FIVE_VIEW_IDENTITY: FORMALIZED
- TRANSITION_DUALITY: FORMALIZED
- IDENTITY_PRESERVATION: FORMALIZED
- MATERIAL_ENDPOINT: SAME TERMINAL OBLIGATION
