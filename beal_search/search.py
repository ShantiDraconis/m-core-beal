#!/usr/bin/env python3
"""
ATK — busca exaustiva de soluções de A^x + B^y = C^z com 1 ≤ A, B, C ≤ N e 3 ≤ x, y, z ≤ M.

Filtro: aritmética módulo um primo p = 2305843009213681573 < 2^61 (vetorizada com numpy).
Toda coincidência módulo p é conferida com inteiros exatos do Python; só soluções exatas são contadas.
Uma solução é PRIMITIVA (contraexemplo de Beal) se gcd(A, B, C) = 1.

uso: python3 search.py N M  →  imprime resumo e grava solutions_N{N}_M{M}.tsv
"""
import math, sys, time
import numpy as np

N, M = int(sys.argv[1]), int(sys.argv[2])
P = 2305843009213681573  # primo < 2^61 (não Mersenne: evita coincidências com potências de 2)
t0 = time.time()

bases, exps, vals = [], [], []
for b in range(1, N + 1):
    for e in range(3, M + 1):
        bases.append(b); exps.append(e); vals.append(pow(b, e, P))
vals = np.array(vals, dtype=np.uint64)
bases = np.array(bases); exps = np.array(exps)

order = np.argsort(vals, kind="stable")
sv = vals[order]
P64 = np.uint64(P)

solutions, coincid = set(), 0
n = len(vals)
for i in range(n):
    s = vals[i] + vals[i:]
    s = np.where(s >= P64, s - P64, s)          # (a + b) mod p, sem estouro (a, b < 2^61)
    pos = np.searchsorted(sv, s)
    pos[pos == n] = n - 1
    hit = np.nonzero(sv[pos] == s)[0]
    for h in hit:
        j = i + h
        A, x, B, y = int(bases[i]), int(exps[i]), int(bases[j]), int(exps[j])
        lhs = A ** x + B ** y
        k = pos[h]
        while k > 0 and sv[k - 1] == s[h]:
            k -= 1
        while k < n and sv[k] == s[h]:
            C, z = int(bases[order[k]]), int(exps[order[k]])
            coincid += 1
            if C ** z == lhs:
                solutions.add((min((A, x), (B, y)), max((A, x), (B, y)), (C, z)))
            k += 1

prim = [s for s in solutions if math.gcd(math.gcd(s[0][0], s[1][0]), s[2][0]) == 1]
dt = time.time() - t0
fn = f"solutions_N{N}_M{M}.tsv"
with open(fn, "w") as f:
    f.write("A\tx\tB\ty\tC\tz\tgcd_ABC\n")
    for (A, x), (B, y), (C, z) in sorted(solutions):
        f.write(f"{A}\t{x}\t{B}\t{y}\t{C}\t{z}\t{math.gcd(math.gcd(A, B), C)}\n")
print(f"N={N} M={M}: termos={n}, pares verificados={n*(n+1)//2}, coincidências mod p={coincid}, "
      f"soluções exatas={len(solutions)}, primitivas (gcd=1)={len(prim)}, tempo={dt:.1f}s")
for s in sorted(solutions)[:8]:
    print("  exemplo:", s, "gcd =", math.gcd(math.gcd(s[0][0], s[1][0]), s[2][0]))
if prim:
    print("PRIMITIVAS:", prim)
