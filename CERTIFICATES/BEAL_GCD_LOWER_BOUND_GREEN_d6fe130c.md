# BEAL GCD LOWER-BOUND PRODUCER — GREEN FROZEN

Status: **GREEN_FROZEN_REDUCTION**
Scientific status: **OPEN_MATH**

Frozen source:
- SHA: `d6fe130c44ef91e0f8ceb6b15a6548f186e381fd`
- Branch: `frozen/gcd-lower-bound-producer-green-d6fe130c`
- Certificate run: `36493742792` — SUCCESS
- Direct Endpoint Rule Guard run: `36493742928` — SUCCESS

## Kernelized producer compression

On the positive `BealData` domain:

```text
(∃ q, CommonDivisor q d.a d.b d.c)
  ↔ 1 < Nat.gcd d.a (Nat.gcd d.b d.c)

CommonPrime d.a d.b d.c
  ↔ 1 < Nat.gcd d.a (Nat.gcd d.b d.c)
```

Therefore the direct producer is:

```text
GCDLowerBoundProducer :=
  ∀ d : BealData, 1 < Nat.gcd d.a (Nat.gcd d.b d.c)
```

and the repository proves:

```text
BealConjecture ↔ GCDLowerBoundProducer
```

## Forward-only status

The frozen K9 layer was restored byte-for-byte and remained protected.
The new reduction lives strictly after K10 in
`lean/MCore/GCDLowerBoundProducer.lean`.

This certificate DOES NOT produce the universal lower bound.
It certifies only that no prime/divisor wrapper is needed beyond this point.

Remaining mathematical obligation:

```text
∀ d : BealData, 1 < gcd(d.a, gcd(d.b,d.c))
```
