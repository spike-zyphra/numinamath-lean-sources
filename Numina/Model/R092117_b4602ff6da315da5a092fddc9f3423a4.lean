import Mathlib

theorem number_theory_286935 (n : ℕ) (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : 2295 / n = 153) :
    n = 15 := by
  interval_cases n <;> norm_num at h₂ ⊢ <;> all_goals trivial