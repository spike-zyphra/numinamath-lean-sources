import Mathlib

open scoped BigOperators

theorem other_49944 (a : ℕ → ℝ)
  (h₀ : a 1 = 1 / 5)
  (h₁ : a 2 = 1 / 5)
  (h₂ : ∀ n ≥ 3, a n = (a (n - 1) + a (n - 2)) / (1 + a (n - 1) * a (n - 2))) :
  IsLeast {n | 1 ≤ n ∧ a n > 1 - 5 ^ (-2022 : ℤ)} 21 := by
  constructor
  · -- Show 21 is in the set
    constructor
    · norm_num
    · -- Compute a 21 and show it's greater than 1 - 5^(-2022)
      norm_num [h₀, h₁, h₂] at *
      all_goals norm_num
  · -- Show that 21 is the smallest
    intro n hn
    rcases hn with ⟨hn1, hnn⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [h₀, h₁, h₂] at hnn <;> norm_num at hnn <;> all_goals
      linarith