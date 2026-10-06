# BEAL TERMINAL INHABITANT-BEHAVIOR CERTIFICATE

Status: BEHAVIOR_CERTIFIED_PENDING_KERNEL / MATERIAL_TERMINAL_OPEN
Head: `8dce92956386c6bcacf84b0d73aa98082b1c203d`

## Behavioral structure captured

The terminal inhabitant-signature is represented by the proposition
`TerminalInhabitantBehavior`, whose fields certify:

- endpoint identity;
- global-root identity;
- reopening idempotence;
- collapse of every positive reopening iterate to the same terminal signature;
- reverse-image collapse;
- forward-after-reverse collapse.

No new mathematical parameter is introduced.

## Minimality

`terminalInhabitantBehavior_minimal` proves the behavioral certificate is
inhabited.

## Boundary

This is an inhabitant of the **behavioral certificate**, not an inhabitant of
`FinalMixedExclusion`.

Therefore:

- BEHAVIORAL_INHABITANT: PRESENT
- SEARCH_DYNAMICS: CLOSED
- TERMINAL_SIGNATURE: FROZEN
- MATERIAL_INHABITANT_OF_FINAL_MIXED_EXCLUSION: OPEN
- BEAL_CONJECTURE: NOT PROMOTED
