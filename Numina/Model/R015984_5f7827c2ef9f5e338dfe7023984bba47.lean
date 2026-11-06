import Mathlib

theorem algebra_322278 {x : ℝ} (hx : x = (x ^ 2 + 3 * x - 2) ^ 2 + 3 * (x ^ 2 + 3 * x - 2) - 2) :
    x = -1 + Real.sqrt 3 ∨ x = -1 - Real.sqrt 3 ∨ x = -2 + Real.sqrt 2 ∨ x = -2 - Real.sqrt 2 := by 
  have h1 : (x ^ 2 + 2 * x - 2) * (x ^ 2 + 4 * x + 2) = 0 := by
    nlinarith [sq_nonneg (x ^ 2 + 3 * x - 2 - x), sq_nonneg (x ^ 2 + 3 * x - 2 + 2), sq_nonneg (x + 1), sq_nonneg (x + 2), sq_nonneg (x ^ 2 + 3 * x - 2), sq_nonneg (x ^ 2 + 4 * x + 2), sq_nonneg (x ^ 2 + 2 * x - 2)]
  cases (mul_eq_zero.mp h1) with
  | inl h2 =>
    have h3 : x ^ 2 + 2 * x - 2 = 0 := h2
    have h4 : (x + 1) ^ 2 = 3 := by
      nlinarith [h3]
    have h5 : x + 1 = Real.sqrt 3 ∨ x + 1 = -Real.sqrt 3 := by
      apply eq_or_eq_neg_of_sq_eq_sq
      norm_num
      linarith [h4]
    cases h5 with
    | inl h6 =>
      have h7 : x = -1 + Real.sqrt 3 := by
        linarith [h6]
      left
      linarith [h7]
    | inr h8 =>
      have h9 : x = -1 - Real.sqrt 3 := by
        linarith [h8]
      right
      left
      linarith [h9]
  | inr h3 =>
    have h4 : x ^ 2 + 4 * x + 2 = 0 := h3
    have h5 : (x + 2) ^ 2 = 2 := by
      nlinarith [h4]
    have h6 : x + 2 = Real.sqrt 2 ∨ x + 2 = -Real.sqrt 2 := by
      apply eq_or_eq_neg_of_sq_eq_sq
      norm_num
      linarith [h5]
    cases h6 with
    | inl h7 =>
      have h8 : x = -2 + Real.sqrt 2 := by
        linarith [h7]
      right
      right
      left
      linarith [h8]
    | inr h8 =>
      have h9 : x = -2 - Real.sqrt 2 := by
        linarith [h8]
      right
      right
      right
      linarith [h9]