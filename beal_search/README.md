# Beal — busca exaustiva de soluções (parâmetro 42)

`search.py N M` lista TODAS as soluções de Aˣ + Bʸ = Cᶻ com 1 ≤ A, B, C ≤ N e 3 ≤ x, y, z ≤ M
(filtro módulo um primo de 61 bits, toda coincidência conferida com inteiros exatos).

| Faixa | Pares (A^x, B^y) verificados | Soluções exatas | Primitivas (gcd(A,B,C) = 1) |
|---|---|---|---|
| A,B,C ≤ 1000, expoentes 3..100 | 4 802 049 000 | 1904 | **0** |
| A,B,C ≤ 10 000, expoentes 3..10 | 3 200 040 000 | 365 | **0** |
| A,B,C ≤ 30 000, expoentes 3..8 | 16 200 090 000 | 491 | **0** |

Todas as soluções encontradas têm fator primo comum, como a conjectura prevê (listas em `solutions_*.tsv`).
Isto é evidência finita: não exclui contraexemplos fora dessas faixas. A exclusão universal continua ABERTA;
no kernel, `ATK.BealDescent.descent_iff_beal` mostra que a descida pedida (parâmetros 64–67) equivale a Beal.
