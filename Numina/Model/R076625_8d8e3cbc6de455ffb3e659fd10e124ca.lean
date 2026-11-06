import Mathlib

theorem algebra_320560 {x1 x2 : ℝ} (hx1 : x1^2 - 4 * x1 + 1 = 0) (hx2 : x2^2 - 4 * x2 + 1 = 0)
    (hx12 : x1 ≠ x2) : x1^3 - 2 * x2^2 + x1 - 1 = 13 + 24 * √3 ∨ x1^3 - 2 * x2^2 + x1 - 1 = 13 - 24 * √3 := by

  have h1 : (x1 - (2 + Real.sqrt 3)) * (x1 - (2 - Real.sqrt 3)) = 0 := by
    nlinarith [Real.sqrt_pos.mpr (show 0 < 3 by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]
  
  have h2 : (x2 - (2 + Real.sqrt 3)) * (x2 - (2 - Real.sqrt 3)) = 0 := by
    nlinarith [Real.sqrt_pos.mpr (show 0 < 3 by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]

  have hx1_eq : x1 = 2 + Real.sqrt 3 ∨ x1 = 2 - Real.sqrt 3 := by
    cases (mul_eq_zero.mp h1) with
    | inl h =>
      left
      linarith
    | inr h =>
      right
      linarith

  have hx2_eq : x2 = 2 + Real.sqrt 3 ∨ x2 = 2 - Real.sqrt 3 := by
    cases (mul_eq_zero.mp h2) with
    | inl h =>
      left
      linarith
    | inr h =>
      right
      linarith
  
  cases hx1_eq with
  | inl h1l =>
    cases hx2_eq with
    | inl h2l =>
      exfalso
      exact hx12 (by linarith)
    | inr h2r =>
      have h3 : x1^3 - 2 * x2^2 + x1 - 1 = 13 + 24 * Real.sqrt 3 := by
        rw [h1l, h2r]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]
      left
      linarith
  | inr h1r =>
    cases hx2_eq with
    | inl h2l =>
      have h4 : x1^3 - 2 * x2^2 + x1 - 1 = 13 - 24 * Real.sqrt 3 := by
        rw [h1r, h2l]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]
      right
      linarith
    | inr h2r =>
      exfalso
      exact hx12 (by linarith)