import Mathlib

open Real

theorem algebra_187840 (x : ℝ) (hx : x ≥ 7 / 2) :
    logb 5 (sqrt (2 * x - 7) + 1) / logb 5 (sqrt (2 * x - 7) + 7) = 0.5 ↔ x = 5.5 := by
  constructor
  · -- Forward direction: if the equation holds, then x = 5.5.
    intro h
    have h1 : sqrt (2 * x - 7) ≥ 0 := Real.sqrt_nonneg (2 * x - 7)
    have h2 : sqrt (2 * x - 7) ^ 2 = 2 * x - 7 := by
      have h3 : 2 * x - 7 ≥ 0 := by linarith
      exact Real.sq_sqrt h3
    -- Ensure the arguments of logarithms are positive
    have h3 : sqrt (2 * x - 7) + 1 > 0 := by
      have h4 : sqrt (2 * x - 7) ≥ 0 := Real.sqrt_nonneg (2 * x - 7)
      linarith
    have h4 : sqrt (2 * x - 7) + 7 > 0 := by
      have h5 : sqrt (2 * x - 7) ≥ 0 := Real.sqrt_nonneg (2 * x - 7)
      linarith
    -- Show that the denominator is non-zero
    have h5 : logb 5 (sqrt (2 * x - 7) + 7) ≠ 0 := by
      by_contra h6
      have h7 : sqrt (2 * x - 7) + 7 = 1 := by
        have h8 : logb 5 (sqrt (2 * x - 7) + 7) = 0 := by linarith
        rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by nlinarith)] at h8
        · linarith
        all_goals linarith
      have h8 : sqrt (2 * x - 7) = -6 := by linarith
      nlinarith [show sqrt (2 * x - 7) ≥ 0 from Real.sqrt_nonneg (2 * x - 7), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * x - 7 by linarith)]
    -- Use the equation to derive A^2 = B
    have h6 : logb 5 (sqrt (2 * x - 7) + 1) = 0.5 * logb 5 (sqrt (2 * x - 7) + 7) := by
      field_simp [h5] at h
      linarith
    have h7 : logb 5 ((sqrt (2 * x - 7) + 1) ^ 2) = logb 5 (sqrt (2 * x - 7) + 7) := by
      have h8 : logb 5 ((sqrt (2 * x - 7) + 1) ^ 2) = 2 * logb 5 (sqrt (2 * x - 7) + 1) := by
        simp [logb_pow]
      have h9 : 2 * logb 5 (sqrt (2 * x - 7) + 1) = logb 5 (sqrt (2 * x - 7) + 7) := by
        linarith [h6]
      linarith [h8, h9]
    -- Remove logarithms by using injectivity
    have h8 : (sqrt (2 * x - 7) + 1) ^ 2 = sqrt (2 * x - 7) + 7 := by
      have h9 : logb 5 ((sqrt (2 * x - 7) + 1) ^ 2) = logb 5 (sqrt (2 * x - 7) + 7) := h7
      have h10 : (sqrt (2 * x - 7) + 1) ^ 2 > 0 := by
        nlinarith [Real.sqrt_nonneg (2 * x - 7)]
      have h11 : sqrt (2 * x - 7) + 7 > 0 := h4
      have h12 : (sqrt (2 * x - 7) + 1) ^ 2 = sqrt (2 * x - 7) + 7 := by
        apply logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h10) (Set.mem_Ioi.mpr h11) h9
      linarith
    -- Solve the equation
    have h9 : (sqrt (2 * x - 7) + 1) ^ 2 = sqrt (2 * x - 7) + 7 := h8
    have h10 : (sqrt (2 * x - 7) + 1) ^ 2 = (sqrt (2 * x - 7)) ^ 2 + 2 * sqrt (2 * x - 7) + 1 := by
      ring
    rw [h10] at h9
    have h11 : (sqrt (2 * x - 7)) ^ 2 = 2 * x - 7 := by
      have h12 : (2 * x - 7) ≥ 0 := by linarith
      exact Real.sq_sqrt h12
    rw [h11] at h9
    have h12 : sqrt (2 * x - 7) = 13 - 2 * x := by
      nlinarith [h9, h1, Real.sqrt_nonneg (2 * x - 7)]
    have h13 : (13 - 2 * x) ≥ 0 := by
      nlinarith [Real.sqrt_nonneg (2 * x - 7), h12, Real.sq_sqrt (show (0 : ℝ) ≤ 2 * x - 7 by linarith)]
    -- Square both sides and solve the resulting quadratic equation
    have h14 : sqrt (2 * x - 7) ^ 2 = 2 * x - 7 := by
      have h15 : (2 * x - 7) ≥ 0 := by linarith
      exact Real.sq_sqrt h15
    have h15 : sqrt (2 * x - 7) = 13 - 2 * x := h12
    have h16 : sqrt (2 * x - 7) ^ 2 = (13 - 2 * x) ^ 2 := by
      rw [h15]
    rw [h14] at h16
    -- The equation is now a polynomial equation
    have h17 : (x - 5.5) * (x - 8) = 0 := by
      ring_nf at h16
      ring_nf
      nlinarith
    cases' (mul_eq_zero.mp h17) with h18 h19
    · -- x - 5.5 = 0
      have h20 : x = 5.5 := by
        linarith
      tauto
    · -- x - 8 = 0
      have h21 : x = 8 := by
        nlinarith
      nlinarith [show x ≤ (6.5 : ℝ) from by nlinarith]
  · -- Backward direction: if x = 5.5, then the equation holds.
    intro h
    rw [h]
    have h1 : sqrt (2 * (5.5 : ℝ) - 7) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : logb 5 (sqrt (2 * (5.5 : ℝ) - 7) + 1) = logb 5 3 := by
      rw [h1]
      norm_num
    have h3 : logb 5 (sqrt (2 * (5.5 : ℝ) - 7) + 7) = logb 5 9 := by
      rw [h1]
      norm_num
    rw [h2, h3]
    have h4 : logb 5 9 = 2 * logb 5 3 := by
      calc
        logb 5 9 = logb 5 (3 ^ 2) := by norm_num
        _ = 2 * logb 5 3 := by simp [logb_pow]
    rw [h4]
    have h5 : logb 5 3 > 0 := by
      apply logb_pos
      all_goals norm_num
    field_simp [h5]
    <;> nlinarith