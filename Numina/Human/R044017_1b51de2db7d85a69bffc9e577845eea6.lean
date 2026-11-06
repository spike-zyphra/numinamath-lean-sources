import Mathlib

/- If $a,b,c$ are integers from the set of positive integers less than $7$ such that \begin{align*}
abc&\equiv 1\pmod 7,\\
5c&\equiv 2\pmod 7,\\
6b&\equiv 3+b\pmod 7,
\end{align*}then what is the remainder when $a+b+c$ is divided by $7$? -/
theorem number_theory_15246 (a b c : ℕ) (ha : a < 7) (hb : b < 7) (hc : c < 7)
    (_ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h1 : a * b * c ≡ 1 [MOD 7]) (h2 : 5 * c ≡ 2 [MOD 7]) (h3 : 6 * b ≡ 3 + b [MOD 7]) :
    (a + b + c) % 7 = 4 := by
  simp_all [Nat.ModEq]
  interval_cases a <;> interval_cases b <;> interval_cases c <;> omega