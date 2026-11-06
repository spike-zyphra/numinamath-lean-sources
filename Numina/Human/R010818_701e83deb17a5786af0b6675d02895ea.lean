import Mathlib

/- Let $n$ be the integer such that $0 \le n < 31$ and $3n \equiv 1 \pmod{31}$. What is $\left(2^n\right)^3 - 2 \pmod{31}$?

Express your answer as an integer from $0$ to $30$, inclusive. -/
theorem number_theory_17010 (n : ℕ) (h₀ : 0 ≤ n) (h₁ : n < 31) (h₂ : 3 * n ≡ 1 [MOD 31]) :
    (2 ^ n) ^ 3 - 2 ≡ 6 [MOD 31] := by
  rw [Nat.ModEq] at h₂ ⊢
  revert n h₂
  decide