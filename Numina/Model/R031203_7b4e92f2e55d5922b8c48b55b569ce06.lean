import Mathlib


theorem algebra_5682 {r : Set ℝ} (hr : r = {x | √((x + 3)^2) = 7 }) :
    r = {4, -10} ∧ (∑x∈{4, -10}, x = -6) := by
  have h1 : r = {4, -10} := by 
    ext x
    simp [hr]
    constructor
    · -- Assume √((x + 3) ^ 2) = 7, show x = 4 ∨ x = -10
      intro h_eq
      have h_eq1 : √((x + 3) ^2) = 7 := h_eq
      have h_eq2 : √((x + 3) ^2) = |x + 3| := by 
        rw [Real.sqrt_sq_eq_abs]
      rw [h_eq2] at h_eq1
      cases eq_or_eq_neg_of_abs_eq h_eq1 with
      | inl h1 =>
        left
        linarith
      | inr h2 =>
        right
        linarith
    · -- Assume x = 4 ∨ x = -10, show √((x + 3) ^2) = 7
      rintro (h | h)
      · -- Assume x = 4, need to show √(( (4 + 3 )) ^2) = 7
        rw [h]
        have h2 : √((4 + 3 : ℝ) ^ 2) = 7 := by
          rw [Real.sqrt_sq_eq_abs]
          rw [abs_of_nonneg (show (4 + 3 : ℝ) ≥ 0 by norm_num)]
          all_goals norm_num
        exact h2
      · -- Assume x = -10, need to show √((-10 + 3 ) ^ 2) = 7
        rw [h]
        have h2 : √((-10 + 3 : ℝ) ^ 2) = 7 := by
          rw [Real.sqrt_sq_eq_abs]
          rw [abs_of_nonpos (show (-10 + 3 : ℝ) ≤ 0 by norm_num)]
          all_goals norm_num
        exact h2
  constructor
  · exact h1
  · -- Show that the sum is -6
    norm_num [Finset.sum_insert, Finset.sum_singleton]