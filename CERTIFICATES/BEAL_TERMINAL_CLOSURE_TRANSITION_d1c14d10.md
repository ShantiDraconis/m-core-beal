# BEAL TERMINAL CLOSURE TRANSITION CERTIFICATE

Status: FORMALIZED_PENDING_KERNEL
Head: `d1c14d107379e66d6066988a6afaeae5ca0c3c79`

## Certified transition

The terminal labels satisfy:

- `OpenMath -> ClosedMath`
- `ClosedMath -> OpenMath`
- `OpenMath <-> ClosedMath`

Because both labels denote the same terminal proposition, the transition is
definitionally the identity and is idempotent.

## Boundary

This proves the transition law, not existence of an inhabitant of OpenMath.
A proof of `OpenMath -> ClosedMath` consumes an `OpenMath` term; it does
not create one from no premises.

- TERMINAL_TRANSITION: PRESENT
- TRANSITION_IDEMPOTENT: PRESENT
- NEW_PARAMETERS: NONE
- MATERIAL_ENDPOINT_INHABITANT: STILL REQUIRED
