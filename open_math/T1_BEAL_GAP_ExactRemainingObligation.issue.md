# T1-BEAL — ExactRemainingObligation

LANE: T1-BEAL  
HEAD: 71a2ff4eefa30e3590da07aa0dc1ff5660697010  
GAP ID: BealEffective.ExactRemainingObligation  
STATUS ATUAL: STRUCTURE GREEN, BUILD GREEN, MATH OPEN_MATH 1.

## Definição exata do que falta

```lean
def ExactRemainingObligation : Prop :=
  ∀ d : BealData, 1 < BealEffective.gcd3 d

def gcd3 (d : BealData) : Nat :=
  Nat.gcd d.a (Nat.gcd d.b d.c)
```

Equivalent frozen producer:

```lean
GCDLowerBoundProducer :=
  ∀ d : BealData, 1 < Nat.gcd d.a (Nat.gcd d.b d.c)
```

## Critério de aceite

- 0 `sorry`
- 0 `admit`
- 0 `axiom` novo
- `lake build MCore` SUCCESS
- source hygiene SUCCESS
- não assumir `BealConjecture`, `CommonPrime`, `GCDLowerBoundProducer` ou `ExactRemainingObligation`
- não usar equivalência do endpoint como produtor

## Rota já GREEN

- `gcd3_pos`
- `gcd3_eq_one_of_not_lowerBound`
- `lowerBound_iff_commonPrime`
- `commonDivisor_iff_one_lt_nestedGCD`
- `commonPrime_iff_one_lt_nestedGCD`
- K9/K10/GCD reduction congelados

## O que não conta

- reabrir `CommonPrime` como hipótese
- reabrir `CommonDivisor` como hipótese
- wrapper equivalente ao GCD target
- conductor/FLT route sem produzir a desigualdade literal
- caso-a-caso finito que não cobre todo `BealData`

## Pedido

Eliminar construtivamente o caso `gcd3 d = 1` para todo `d : BealData`, usando apenas fatos aritméticos já GREEN e matemática nova que derive uma contradição a partir da equação de Beal e dos expoentes > 2.
