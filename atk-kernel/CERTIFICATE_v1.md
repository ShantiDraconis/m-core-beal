# Certificado ATK v1 — ShantiDraconis/m-core-beal

- Commit verificado: `54876fcc1c11f978c3d31784b218d6a074a08192` (tag `atk-kernel-cert-v1`)
- Gerado em: 2026-10-11T23:51:48+00:00
- Teoremas aceitos pelo kernel: **1/1**

## ATK kernel check
- Execução: https://github.com/ShantiDraconis/m-core-beal/actions/runs/38181945225
- Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)
- SHA-256 das fontes: `ea487d12952a43a7c51bbc3a4596fe3aa647e576277b10ce7baa9c3fd7df521d`
- Job “Lean 4 + Mathlib — compilação e auditoria de axiomas”: success

| Teorema | Veredito | Axiomas |
|---|---|---|
| `ATK.Beal.exponent_gcd_le_two` | ✅ CERTIFIED  | propext, Classical.choice, Quot.sound |

Lemas auxiliares e cálculos concretos. Nenhuma das sete conjecturas foi provada; OPEN_MATH=true.
