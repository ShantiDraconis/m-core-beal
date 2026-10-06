# BEAL RPA DUAL ENDPOINT CERTIFICATE

Status: FORMALIZED_PENDING_KERNEL
Head: `832fd9671132045ff41f8feb36491f39b9d61bc2`

## Corrected model

The RPA state contains two distinct endpoint positions:

- `OpenEndpoint` tagged `openSide`
- `ClosedEndpoint` tagged `closedSide`

Their tags are provably distinct, while their payloads satisfy:

`OpenMath ↔ ClosedMath`.

The certificate therefore preserves both structural distinction and logical
identity.

## Simultaneous coexistence

`DualEndpointState` contains:

- the open endpoint;
- the closed endpoint;
- the logical equivalence of their payloads;
- forward identity-preserving transport;
- backward identity-preserving transport.

The state cannot be constructed with only one side.

## Exact strength

`Nonempty DualEndpointState ↔ Nonempty Endpoint`.

Thus the corrected RPA state is exactly as strong as the terminal mathematical
payload; it does not erase endpoint distinction and does not manufacture the
payload.

- OPEN_ENDPOINT_POSITION: DISTINCT
- CLOSED_ENDPOINT_POSITION: DISTINCT
- LOGICAL_IDENTITY: PRESERVED
- DUAL_COEXISTENCE: REQUIRED
- STRUCTURAL_GAPS: 0
- MATERIAL_ENDPOINT: SAME TERMINAL OBLIGATION
