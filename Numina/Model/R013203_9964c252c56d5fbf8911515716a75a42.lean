import Mathlib

theorem algebra_180036 {x y : ℝ} (h1 : (x^2 + y) * 2^(y - x^2) = 1) (h2 : 9 * (x^2 + y) = 6^(x^2 - y)) :
    (x = Real.sqrt 3 ∧ y = 1) ∨ (x = -Real.sqrt 3 ∧ y = 1) := by
  have eq3 : x^2 + y = (2 : ℝ) ^ (x^2 - y) := by
    have eq4 : (x^2 + y) * (2 : ℝ) ^ (y - x^2) = 1 := h1
    have eq6 : x^2 + y = (1 : ℝ) / ((2 : ℝ) ^ (y - x^2)) := by 
      field_simp
      linarith
    -- Now transform eq6
    have eq7 : (1 : ℝ) / ((2 : ℝ) ^ (y - x^2)) = (2 : ℝ) ^ (x^2 - y) := by
      have h3' : (1 : ℝ) / ((2 : ℝ) ^ (y - x^2)) = (2 : ℝ) ^ (- (y - x^2 : ℝ)) := by
        have eq5 : (2 : ℝ) ^ (- (y - x^2 : ℝ) ) = ((2 : ℝ) ^ (y - x^2))⁻¹ := by
          rw [Real.rpow_neg]
          all_goals norm_num
        have eq6' : (1 : ℝ) / ((2 : ℝ) ^ (y - x^2) ) = ((2 : ℝ) ^ (y - x^2))⁻¹ := by
          field_simp
        rw [eq6']
        rw [eq5]
      rw [h3']
      have eq8 : - (y - x^2 : ℝ) = x^2 - y := by ring
      rw [eq8]
    rw [eq7] at eq6
    linarith
  have eq4 : (6 : ℝ) ^ (x^2 - y) = (2 : ℝ) ^ (x^2 - y) * (3 : ℝ) ^ (x^2 - y) := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num]
    rw [← Real.mul_rpow]
    all_goals linarith
  have eq7 : 9 * (x^2 + y) = (2 : ℝ) ^ (x^2 - y) * (3 : ℝ) ^ (x^2 - y) := by
    rw [eq4] at h2
    linarith
  rw [eq3] at eq7
  have eq9 : (2 : ℝ) ^ (x^2 - y) ≠ 0 := by positivity
  have eq10 : (3 : ℝ) ^ (x^2 - y) = 9 := by
    apply (mul_left_inj' eq9).mp
    linarith
  have eq11 : x^2 - y = (2 : ℝ) := by
    have eq12 : (3 : ℝ) ^ (x^2 - y) = 9 := eq10
    have eq13 : (3 : ℝ) ^ (x^2 - y) = (3 : ℝ) ^ (2 : ℝ) := by
      rw [eq12]
      norm_num
    have eq14 : x^2 - y = (2 : ℝ) := by
      apply_fun (Real.logb 3) at eq13
      have h3 : Real.logb 3 ((3 : ℝ) ^ (x^2 - y)) = x^2 - y := by
        rw [Real.logb_rpow]
        all_goals norm_num
      have h4 : Real.logb 3 ((3 : ℝ) ^ (2 : ℝ)) = (2 : ℝ) := by
        rw [Real.logb_rpow]
        all_goals norm_num
      linarith [h3, h4, eq13]
    linarith
  have eq18 : x^2 + y = (4 : ℝ) := by
    rw [eq3]
    rw [eq11]
    norm_num
  have eq19 : y = x^2 - 2 := by
    nlinarith [eq11]
  have eq20 : x^2 = 3 := by
    rw [eq19] at eq18
    nlinarith
  have h3 : x = Real.sqrt 3 ∨ x = -Real.sqrt 3 := by
    have h4 : x^2 = 3 := eq20
    have h5 : x^2 - 3 = 0 := by nlinarith
    have h7 : (x - Real.sqrt 3) * (x + Real.sqrt 3) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    cases (mul_eq_zero.1 h7) with
    | inl h8 =>
      left
      linarith
    | inr h9 =>
      right
      linarith
  have h10 : y = 1 := by
    rw [eq20] at eq19
    nlinarith
  cases h3 with
  | inl hx =>
    left
    constructor
    · -- x = Real.sqrt 3
      linarith
    · -- y = 1
      linarith
  | inr hx =>
    right
    constructor
    · -- x = -Real.sqrt 3
      linarith
    · -- y = 1
      linarith