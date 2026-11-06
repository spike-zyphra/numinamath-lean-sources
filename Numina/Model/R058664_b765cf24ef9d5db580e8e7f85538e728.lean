import Mathlib

theorem number_theory_18655 (n : ℕ) (h₀ : n > 0) (h₁ : n < 100) (h₂ : n > 9)
    (h₃ : n = 2 * (Nat.digits 10 n).sum) :
    n = 18 := by
  interval_cases n <;> norm_num at h₃ <;> try { tauto }