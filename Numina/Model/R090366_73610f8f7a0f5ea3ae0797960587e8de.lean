import Mathlib

theorem number_theory_325346 (n : ℕ) (h₀ : Nat.Prime n) (h₁ : n < 100) (h₂ : n > 9)
    (h₃ : Nat.Prime (n + 20180500)) :
    n = 61 := by
  interval_cases n <;> norm_num at h₀ h₁ h₂ h₃ <;> try trivial