import Mathlib

theorem algebra_11190 {x y : ℝ} (h₀ : |x - y| = 3) (h₁ : x + y = 31) :
    max x y = 17 := by
  cases eq_or_eq_neg_of_abs_eq h₀ with
  | inl h2 =>
    -- Case where x - y = 3
    have h3 : x = 17 := by
      linarith
    have h4 : y = 14 := by
      linarith [h₁, h3]
    rw [h3, h4]
    norm_num
  | inr h2 =>
    -- Case where -(x - y) = 3, which means y - x = 3
    have h3 : x = 14 := by
      linarith
    have h4 : y = 17 := by
      linarith [h₁, h3]
    rw [h3, h4]
    norm_num