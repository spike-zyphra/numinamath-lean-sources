import Mathlib

theorem number_theory_151516 (n : ℕ) (h₀ : n < 1000) (h₁ : (Nat.digits n 1987).length = 3)
    (h₂ : (Nat.digits n 1987).sum = 25) :
    n = 19 := by 
  interval_cases n <;> norm_num at h₁ h₂ ⊢ <;> try { contradiction } <;> try { trivial }