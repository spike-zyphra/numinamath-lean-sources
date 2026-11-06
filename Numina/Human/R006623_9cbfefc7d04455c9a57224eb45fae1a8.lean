import Mathlib
/- Let $a, b, c, d$ be distinct decimal digits, where a digit is an integer from 0 to 9. Assume $a \neq 0$ and $c \neq 0$.
Let $N_639343 = a \cdot 10^3 + b \cdot 10^2 + c \cdot 10^1 + d$.
Let $N_639343 = c \cdot 10^3 + d \cdot 10^2 + a \cdot 10^1 + b$.
Theorem: If $50 \cdot N_639343 = 51 \cdot N_2$, then $N_639343 = 5049$. -/
theorem number_theory_639343 (a b c d : ℕ) (ha1 : 1 ≤ a) (ha2 : a ≤ 9) (hb : b ≤ 9) (hc1 : 1 ≤ c) (hc2 : c ≤ 9) (hd : d ≤ 9) (h : 50 * (a * 10 ^ 3 + b * 10 ^ 2 + c * 10 + d) = 51 * (c * 10 ^ 3 + d * 10 ^ 2 + a * 10 + b)) : a * 10 ^ 3 + b * 10 ^ 2 + c * 10 + d = 5049:= by omega

