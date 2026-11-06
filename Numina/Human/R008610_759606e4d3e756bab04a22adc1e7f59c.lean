import Mathlib

/- If $a,b,c$ are non-negative integers less than $7$ such that \begin{align*}
a+2b+3c&\equiv 0\pmod 7,\\
2a+3b+c&\equiv 4\pmod 7,\\
3a+b+2c&\equiv 4\pmod 7,
\end{align*}then determine the remainder when $abc$ is divided by $7$. -/
theorem number_theory_16038 (a b c : ℕ) (ha : a < 7) (hb : b < 7) (hc : c < 7)
    (h1 : a + 2 * b + 3 * c ≡ 0 [MOD 7]) (h2 : 2 * a + 3 * b + c ≡ 4 [MOD 7])
    (h3 : 3 * a + b + 2 * c ≡ 4 [MOD 7]) :
    a * b * c ≡ 6 [MOD 7] := by
  simp [Nat.ModEq] at *
  interval_cases a <;> interval_cases b <;> interval_cases c <;> omega