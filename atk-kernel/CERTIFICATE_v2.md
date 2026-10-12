# Certificado ATK v2 — ShantiDraconis/m-core-beal

- Commit verificado: `48440ab2871eb574009d09ca2f4e522f69eecd17` (tag `atk-kernel-cert-v2`)
- Gerado em: 2026-10-12T00:46:23+00:00
- Teoremas aceitos pelo kernel: **5/5**

## ATK kernel check
- Execução: https://github.com/ShantiDraconis/m-core-beal/actions/runs/38188854616
- Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)
- SHA-256 das fontes: `5f25941c5ee341e3f4900b17e5cffa32ec994ab284f8a1f0e8533ba338293e57`
- Job “Lean 4 + Mathlib — compilação e auditoria de axiomas”: success

| Teorema | Veredito | Axiomas |
|---|---|---|
| `ATK.BealDescent.no_primitive_of_descent` | ✅ CERTIFIED  | propext |
| `ATK.BealDescent.beal_of_descent` | ✅ CERTIFIED  | propext, Quot.sound |
| `ATK.BealDescent.descent_of_beal` | ✅ CERTIFIED  | propext, Quot.sound |
| `ATK.BealDescent.descent_iff_beal` | ✅ CERTIFIED  | propext, Quot.sound |
| `ATK.Beal.exponent_gcd_le_two` | ✅ CERTIFIED  | propext, Classical.choice, Quot.sound |

Lemas auxiliares e cálculos concretos. Nenhuma das sete conjecturas foi provada; OPEN_MATH=true.
