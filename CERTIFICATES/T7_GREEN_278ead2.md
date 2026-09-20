# T7 GREEN Certificate — Exponent Normalization

## Immutable checkpoint

- Frozen SHA: `278ead2946e422708a465e2a9fe31332b0574446`
- Frozen branch: `frozen/t7-green-278ead2`
- GitHub Actions run: `35502830446`
- Job: `106057535072`
- Conclusion: `success`

## Certified scope

`T7_exponent_reduction` proves constructively that every natural exponent
`n > 2` admits
`n = r*k` where `r > 2` and either `r = 4` or `r` satisfies the
local elementary `IsPrime` predicate.

The proof reuses the certified K10 prime-divisor kernel and reports only
`[propext, Quot.sound]`; no `sorryAx` or `Classical.choice`.

## Consequence for the attack

A primitive Beal candidate can now be attacked through reduced signatures
whose exponents are drawn from `4` or primes greater than `2`.
The next required bridge is not yet certified: after rewriting
`A^x = (A^k)^r`, etc., primitiveness must be transported to the powered
bases. That requires a certified prime-divides-power / prime-support lemma.

## Preservation rule

`frozen/t7-green-278ead2` remains fixed at
`278ead2946e422708a465e2a9fe31332b0574446`.
