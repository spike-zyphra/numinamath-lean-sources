import Mathlib

theorem algebra_120839 (x : ℝ) (hx : x ≠ 0) :
    x + x / Real.sqrt (x ^ 2 - 1) = 35 / 12 ↔
    x = 5 / 4 ∨ x = 5 / 3 := by 
  constructor
  · -- Forward direction: If the equation holds, then x is one of the roots
    intro h_eq
    have h1 : x^2 - 1 > 0 := by
      by_contra h
      push_neg at h
      have h7 : Real.sqrt (x ^ 2 - 1) = 0 := by
        rw [Real.sqrt_eq_zero']
        nlinarith
        all_goals nlinarith
      rw [h7] at h_eq
      have hx2 : x = 35 / 12 := by
        norm_num [show x / (0 : ℝ) = 0 by simp] at h_eq ⊢
        linarith
      nlinarith [sq_nonneg (x - 35 / 12), hx2]
    have h6 : Real.sqrt (x ^ 2 - 1) > 0 := by 
      apply Real.sqrt_pos.mpr
      linarith
    have h3 : x > 0 := by
      by_contra h3
      push_neg at h3
      have h4 : x ≤ (0 : ℝ) := by linarith
      have h5 : x / Real.sqrt (x ^ 2 - 1) ≤ 0 := by 
        have h6 : Real.sqrt (x ^ 2 - 1) > 0 := h6
        apply div_nonpos_of_nonpos_of_nonneg
        · -- Show x ≤ 0.
          nlinarith
        · -- Show √(x^2-1) ≥ 0.
          positivity
      have h6' : x + x / Real.sqrt (x ^ 2 - 1) ≤ 0 := by 
        linarith
      nlinarith [h_eq, h6', Real.sqrt_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2), sq_pos_of_pos (show 0 < (x ^2 -1 : ℝ) from by nlinarith)]
    -- Algebra to derive the quadratic
    have eq1 : x * Real.sqrt (x ^2 - 1) + x = (35 / 12) * Real.sqrt (x ^2 - 1) := by
      have h8 : Real.sqrt (x ^ 2 - 1) > 0 := h6
      have eq2 : x + x / Real.sqrt (x ^ 2 - 1) = 35 / 12 := by linarith [h_eq]
      field_simp [h8] at eq2 ⊢
      nlinarith [h_eq, Real.sqrt_nonneg (x ^ 2 - 1)]
    -- To simplify the equation for solving a quadratic
    have eq4 : (x - 5 / 4) * (x - 5 / 3) = 0 := by
      nlinarith [sq_nonneg (x^2 - 1 - 25 / 16), sq_nonneg (x^2 - 1 - 16 / 9), Real.sq_sqrt (show (0 : ℝ) ≤ x^2 - 1 by nlinarith), sq_nonneg (x - 5 / 4), sq_nonneg (x - 5 / 3), Real.sqrt_nonneg (x^2 -1), sq_nonneg (x * Real.sqrt (x ^ 2 - 1)), sq_nonneg ((Real.sqrt (x ^ 2 - 1)) ^ 2 - x ^ 2)]
    cases' (mul_eq_zero.mp eq4) with h8 h9
    · -- First case: x = 5/4
      left
      linarith
    · -- Second case: x = 5/3
      right
      linarith
  · -- Backward direction: If x is one of the roots, then the equation holds
    rintro (h_eq | h_eq)
    · -- First direction: x = 5/4
      rw [h_eq]
      have h6 : Real.sqrt ((5 / 4 : ℝ) ^2 - 1) = 3 / 4 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> nlinarith
      rw [h6]
      field_simp [h6]
      <;> norm_num
    · -- Second direction: x = 5/3
      rw [h_eq]
      have h7 : Real.sqrt ((5 / 3 : ℝ) ^ 2 - 1) = 4 / 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> nlinarith
      rw [h7]
      field_simp [h7]
      <;> norm_num