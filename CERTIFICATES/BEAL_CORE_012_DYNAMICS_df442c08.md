# BEAL CORE 0-1-2 DYNAMICS CERTIFICATE

Status: STRUCTURAL_DYNAMICS_PENDING_KERNEL
Head: `df442c08fb5d4329096272c0747c6f96fd6f176d`

## Three-state terminal code

The search dynamics are represented by:

- LEFT  = 0
- CORE  = 1
- RIGHT = 2

Certified structural laws:

- reverse swaps LEFT/RIGHT and fixes CORE;
- reverse is involutive;
- tension sends every state to CORE;
- tension is idempotent;
- reverse followed by tension returns CORE;
- reverse-tension-reverse returns CORE.

This certifies the user's proposed contraction/repulsion/torsion picture as a
finite structural dynamics with no fourth state and no new parameter after
the terminal frontier.

## Boundary

This certificate concerns search dynamics. It does not itself construct
`FinalMixedExclusion`.

- CORE_DYNAMICS: CERTIFIED_PENDING_KERNEL
- NEW_STATES_AFTER_CORE: NONE
- STRUCTURAL_REOPEN: FORBIDDEN
- MATERIAL_TERMINAL_PRODUCER: OPEN
