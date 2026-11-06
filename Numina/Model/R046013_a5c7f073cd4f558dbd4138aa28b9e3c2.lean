import Mathlib

theorem algebra_302836 {x1 x2 : ℝ} (hx1 : (x1 - 3)^2 - 2 = 0) (hx2 : (x2 - 3)^2 - 2 = 0)
    (hxy : x1 ≠ x2) :
    (Real.sqrt (x1 * x2) + x1) / (x2 + Real.sqrt (x1 * x2)) +
    (Real.sqrt (x1 * x2) - x2) / (x1 - Real.sqrt (x1 * x2)) =
    6 * Real.sqrt 7 / 7 := by

  have h1 : (x1 - 3) ^ 2 = 2 := by linarith
  have h2 : (x2 - 3) ^ 2 = 2 := by linarith

  have h3 : x1 = 3 + Real.sqrt 2 ∨ x1 = 3 - Real.sqrt 2 := by
    have h4 : (x1 - 3) ^ 2 = 2 := h1
    have h5 : (x1 - 3) ^ 2 - 2 = 0 := by linarith
    have h6 : (x1 - 3 - Real.sqrt 2) * (x1 - 3 + Real.sqrt 2) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    cases (mul_eq_zero.mp h6) with
    | inl h7 =>
      left
      linarith
    | inr h8 =>
      right
      linarith

  have h4 : x2 = 3 + Real.sqrt 2 ∨ x2 = 3 - Real.sqrt 2 := by
    have h5 : (x2 - 3) ^ 2 = 2 := h2
    have h6 : (x2 - 3) ^ 2 - 2 = 0 := by linarith
    have h7 : (x2 - 3 - Real.sqrt 2) * (x2 - 3 + Real.sqrt 2) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    cases (mul_eq_zero.mp h7) with
    | inl h8 =>
      left
      linarith
    | inr h9 =>
      right
      linarith

  cases h3 with
  | inl hx1_pos =>
    cases h4 with
    | inl hx2_pos =>
      exfalso
      exact hxy (by linarith)
    | inr hx2_neg =>
      have hx1_eq : x1 = 3 + Real.sqrt 2 := hx1_pos
      have hx2_eq : x2 = 3 - Real.sqrt 2 := hx2_neg
      have hprod : x1 * x2 = 7 := by
        rw [hx1_eq, hx2_eq]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have hsqrt : Real.sqrt (x1 * x2) = Real.sqrt 7 := by
        rw [hprod]
      rw [hsqrt]
      rw [hx1_eq, hx2_eq]
      have h1 : Real.sqrt 7 ≥ 0 := Real.sqrt_nonneg 7
      have h2 : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
      field_simp [(show (3 - Real.sqrt 2 + Real.sqrt 7) ≠ 0 by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (7 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]),
       (show (3 + Real.sqrt 2 - Real.sqrt 7) ≠ 0 by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (7 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)])]
      ring_nf
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (7 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), mul_self_nonneg (Real.sqrt 7 - Real.sqrt 2), mul_self_nonneg (Real.sqrt 7 + Real.sqrt 2)]
  | inr hx1_neg =>
    cases h4 with
    | inl hx2_pos =>
      have hx1_eq : x1 = 3 - Real.sqrt 2 := hx1_neg
      have hx2_eq : x2 = 3 + Real.sqrt 2 := hx2_pos
      have hprod : x1 * x2 = 7 := by
        rw [hx1_eq, hx2_eq]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have hsqrt : Real.sqrt (x1 * x2) = Real.sqrt 7 := by
        rw [hprod]
      rw [hsqrt]
      rw [hx1_eq, hx2_eq]
      have h1 : Real.sqrt 7 ≥ 0 := Real.sqrt_nonneg 7
      have h2 : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
      field_simp [(show (3 + Real.sqrt 2 + Real.sqrt 7) ≠ 0 by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (7 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]),
       (show (3 - Real.sqrt 2 - Real.sqrt 7) ≠ 0 by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (7 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)])]
      ring_nf
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (7 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), mul_self_nonneg (Real.sqrt 7 - Real.sqrt 2), mul_self_nonneg (Real.sqrt 7 + Real.sqrt 2)]
    | inr hx2_neg =>
      exfalso
      exact hxy (by linarith)