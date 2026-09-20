# T6 GREEN Certificate — Exact Primitive Scientific Frontier

## Immutable checkpoint

- Frozen SHA: `466a6ec4cc3afe367408c76c5d085c42ee36c093`
- Frozen branch: `frozen/t6-green-466a6ec`
- GitHub Actions run: `35502709020`
- Job: `106057212481`
- Conclusion: `success`

## Certified scope

- `T6PrimitiveSolution` packages exactly a positive integer solution of
  `a^x + b^y = c^z` with `x,y,z > 2` and no nontrivial common divisor.
- `T6ScientificFrontier := ¬ Nonempty T6PrimitiveSolution`.
- `T6_T4_iff_no_primitive` is axiom-free.
- `T6_beal_iff_frontier` certifies the exact chain
  `BealConjecture ↔ V0 ↔ T3 ↔ T4 ↔ T6ScientificFrontier`.

The printed axiom footprint for the final equivalence is only
`[propext, Quot.sound]`; no `sorryAx` or `Classical.choice`.

## Scientific boundary

This checkpoint does not establish `T6ScientificFrontier`.
The next genuine mathematical task is to rule out an inhabitant of
`T6PrimitiveSolution` by new arithmetic input. Repackaging the same
proposition is not eligible for FINAL_PROOF promotion.

## Preservation rule

`frozen/t6-green-466a6ec` remains fixed at
`466a6ec4cc3afe367408c76c5d085c42ee36c093`.
