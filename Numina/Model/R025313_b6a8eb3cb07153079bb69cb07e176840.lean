import Mathlib

open Real

theorem inequalities_10295 :
    (∀ a b : ℝ, a > b → |a| > b) ∧ ¬(∀ a b : ℝ, |a| > b → a > b) := by
  constructor
  · -- Proof that ∀ a b : ℝ, a > b → |a| > b
    intro a b h
    by_cases h1 : a ≥ 0
    · -- Case a ≥ 0
      rw [abs_of_nonneg h1]
      linarith
    · -- Case a < 0
      rw [abs_of_neg (lt_of_not_ge h1)]
      linarith
  · -- Proof that ¬(∀ a b : ℝ, |a| > b → a > b)
    intro h
    have h1 := h (-1 : ℝ) (-0.5 : ℝ)
    norm_num [abs] at h1 ⊢
    all_goals linarith