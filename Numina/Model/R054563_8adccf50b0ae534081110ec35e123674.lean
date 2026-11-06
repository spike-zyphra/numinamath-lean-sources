import Mathlib

theorem algebra_2607 (a b : ℝ) (h₀ : abs a - abs b = 1) (h₁ : 3 * abs a = 4 * abs b) :
    abs (a - b) = 7 ∨ abs (a - b) = 1 := by 
  have h2 : abs a = 4 := by 
    have h3 : abs b = 3 := by 
      linarith [abs_nonneg a, abs_nonneg b, h₀, h₁]
    linarith [h₁, h3]
  have h3 : abs b = 3 := by
    linarith [abs_nonneg a, abs_nonneg b, h₀, h₁]

  cases' eq_or_eq_neg_of_abs_eq h2 with h4 h4
  · -- case a = 4
    cases' eq_or_eq_neg_of_abs_eq h3 with h5 h5
    · -- case b = 3
      have : abs (a - b) = 1 := by
        rw [h4, h5]
        norm_num
      right
      linarith
    · -- case b = -3
      have : abs (a - b) = 7 := by
        rw [h4, h5]
        norm_num
      left
      linarith
  · -- case a = -4
    cases' eq_or_eq_neg_of_abs_eq h3 with h5 h5
    · -- case b = 3
      have : abs (a - b) = 7 := by
        rw [h4, h5]
        norm_num
      left
      linarith
    · -- case b = -3
      have : abs (a - b) = 1 := by
        rw [h4, h5]
        norm_num
      right
      linarith