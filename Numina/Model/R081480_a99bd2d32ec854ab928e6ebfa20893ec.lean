import Mathlib

theorem number_theory_166097 (n : ℕ) (h₀ : 10 ≤ n) (h₁ : n < 49) :
    (2 * n).digits 10 = [a, b] → a * 10 + b + 2 = 44 := by
  rintro h2
  interval_cases n <;> norm_num at h2 ⊢ <;> simp [Nat.digits, Nat.digitsAux] at h2 ⊢ <;> omega