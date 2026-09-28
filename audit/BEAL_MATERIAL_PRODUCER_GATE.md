# Beal MATERIAL_PRODUCER_GATE v1

`CommonPrimeWitnessContract` contains the whole terminal producer:

```lean
structure CommonPrimeWitnessContract where
  witness : ∀ d : BealData, CommonPrime d.a d.b d.c
```

Thus `witness_contract_closes_beal` is GREEN_TRANSPORT only.

## Stable hole

```
∀ d : BealData, CommonPrime d.a d.b d.c
```

must be derived from the equation and arithmetic hypotheses in `BealData`,
without receiving the common-prime conclusion as data.

AUDIT_STATUS = GREEN
MATERIAL_STATUS = OPEN_MATH
MATERIAL_GREEN = false
