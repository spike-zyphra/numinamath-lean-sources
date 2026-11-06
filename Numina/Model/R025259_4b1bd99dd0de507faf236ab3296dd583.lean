import Mathlib

theorem algebra_306344 (a b c : ℝ) (h₀ : a ≠ b) (h₁ : b ≠ c) (h₂ : a ≠ c) :
    ∃ x, x^2 = (a - b)^2 ∨ x^2 = (b - c)^2 ∨ x^2 = (c - a)^2 ∧ x^2 ≤ (a^2 + b^2 + c^2) / 2 := by
  by_cases h3 : (a - b)^2 ≤ (a^2 + b^2 + c^2) / 2
  · -- if (a-b)^2 is less, then we can take it
    use a - b
    left
    rfl
  · -- else, need to check others
    by_cases h4 : (b - c)^2 ≤ (a^2 + b^2 + c^2) / 2
    · -- if (b-c)^2 is less, then we can take it
      use b - c
      right
      left
      rfl
    · -- else, need to prove that (c-a)^2 is the one
      have h5 : (c - a)^2 ≤ (a^2 + b^2 + c^2) / 2 := by
        by_contra h
        push_neg at h
        nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by intro h'; apply h₀; linarith),
          sq_pos_of_ne_zero (show (b - c) ≠ 0 by intro h'; apply h₁; linarith),
          sq_pos_of_ne_zero (show (c - a) ≠ 0 by intro h'; apply h₂; linarith),
          sq_nonneg (a + b + c),
          sq_nonneg (a - b),
          sq_nonneg (b - c),
          sq_nonneg (c - a)]
      use c - a
      simp [h5]