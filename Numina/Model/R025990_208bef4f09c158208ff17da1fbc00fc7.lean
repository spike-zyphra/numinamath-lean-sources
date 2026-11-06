import Mathlib

theorem algebra_285277 : 400 * (Real.cos (Real.pi / 12) ^ 5 + Real.sin (Real.pi / 12) ^ 5) / (Real.cos (Real.pi / 12) + Real.sin (Real.pi / 12)) = 275 := by
  have h1 : Real.cos (Real.pi / 12) + Real.sin (Real.pi / 12) ≠ 0 := by
    have h2 : Real.cos (Real.pi / 12) + Real.sin (Real.pi / 12) > 0 := by
      have hcos : Real.cos (Real.pi / 12) > 0 := by
        apply Real.cos_pos_of_mem_Ioo
        constructor
        · linarith [Real.pi_pos]
        · linarith [Real.pi_pos]
      have hsin : Real.sin (Real.pi / 12) > 0 := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · linarith [Real.pi_pos]
        · linarith [Real.pi_pos]
      nlinarith [Real.cos_le_one (Real.pi / 12), Real.sin_le_one (Real.pi / 12), Real.sin_sq_add_cos_sq (Real.pi / 12)]
    nlinarith
  -- rewrite the numerator by factoring
  have h3 : Real.cos (Real.pi / 12) ^ 5 + Real.sin (Real.pi / 12) ^ 5 =
          (Real.cos (Real.pi / 12) + Real.sin (Real.pi / 12)) *
          (Real.cos (Real.pi / 12) ^ 4 - Real.cos (Real.pi / 12) ^ 3 * Real.sin (Real.pi / 12) +
          Real.cos (Real.pi / 12) ^ 2 * Real.sin (Real.pi / 12) ^ 2 -
          Real.cos (Real.pi / 12) * Real.sin (Real.pi / 12) ^ 3 + Real.sin (Real.pi / 12) ^ 4) := by
    ring_nf
    <;> 
    simp [pow_two, pow_succ, mul_add]
    <;> 
    ring_nf
    <;> 
    norm_num [Real.sin_sq, Real.cos_sq]
    all_goals
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi / 12)]
  -- simplify the original expression
  have h4 : 400 * (Real.cos (Real.pi / 12) ^ 5 + Real.sin (Real.pi / 12) ^ 5) / (Real.cos (Real.pi / 12) + Real.sin (Real.pi / 12)) =
          400 * (Real.cos (Real.pi / 12) ^ 4 - Real.cos (Real.pi / 12) ^ 3 * Real.sin (Real.pi / 12) + Real.cos (Real.pi / 12) ^ 2 * Real.sin (Real.pi / 12) ^ 2 - Real.cos (Real.pi / 12) * Real.sin (Real.pi / 12) ^ 3 + Real.sin (Real.pi / 12) ^ 4) := by
    rw [h3]
    field_simp [h1]
    <;> nlinarith
  -- exact values of cos(pi/12) and sin(pi/12)
  have h5 : Real.cos (Real.pi / 12) = (Real.sqrt 2 / 4) * (Real.sqrt 3 + 1) := by
    have h1 : Real.cos (Real.pi / 12) = Real.cos (Real.pi / 4 - Real.pi / 6) := by
      ring_nf
    rw [h1]
    rw [Real.cos_sub]
    have h2 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    have h3 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
    have h4 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := by
      exact Real.cos_pi_div_six
    have h5 : Real.sin (Real.pi / 6) = 1 / 2 := by
      exact Real.sin_pi_div_six
    rw [h2, h3, h4, h5]
    ring_nf
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    all_goals
      ring_nf
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  -- exact values of sin(pi/12)
  have h6 : Real.sin (Real.pi / 12) = (Real.sqrt 2 / 4) * (Real.sqrt 3 - 1) := by
    have h1 : Real.sin (Real.pi / 12) = Real.sin (Real.pi / 4 - Real.pi / 6) := by
      ring_nf
    rw [h1]
    rw [Real.sin_sub]
    have h2 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
    have h3 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    have h4 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := by
      exact Real.cos_pi_div_six
    have h5 : Real.sin (Real.pi / 6) = 1 / 2 := by
      exact Real.sin_pi_div_six
    rw [h2, h3, h4, h5]
    ring_nf
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    all_goals
      ring_nf
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  -- substitute the exact values 
  rw [h4]
  rw [h5, h6]
  -- perform algebraic simplification
  have h7 : (Real.sqrt 2 / 4 * (Real.sqrt 3 + 1) : ℝ) ^ 2 = (Real.sqrt 2 ^ 2 / 16 * (Real.sqrt 3 + 1) ^ 2 : ℝ) := by
    ring_nf
  have h8 : (Real.sqrt 2 / 4 * (Real.sqrt 3 - 1) : ℝ) ^ 2 = (Real.sqrt 2 ^ 2 / 16 * (Real.sqrt 3 - 1) ^ 2 : ℝ) := by
    ring_nf
  -- highest powers first, then lower powers as needed by norm_num
  have h9 : (Real.sqrt 2 / 4 * (Real.sqrt 3 + 1) : ℝ) ^ 3 = (Real.sqrt 2 ^ 3 / 64 * (Real.sqrt 3 + 1) ^ 3 : ℝ) := by
    ring_nf
  have h10 : (Real.sqrt 2 / 4 * (Real.sqrt 3 + 1) : ℝ) ^ 4 = (Real.sqrt 2 ^ 4 / 256 * (Real.sqrt 3 + 1) ^ 4 : ℝ) := by
    ring_nf
  have h11 : (Real.sqrt 2 / 4 * (Real.sqrt 3 - 1) : ℝ) ^ 3 = (Real.sqrt 2 ^ 3 / 64 * (Real.sqrt 3 - 1) ^ 3 : ℝ) := by
    ring_nf
  -- products of c and s
  have h12 : (Real.sqrt 2 / 4 * (Real.sqrt 3 + 1) : ℝ) * (Real.sqrt 2 / 4 * (Real.sqrt 3 - 1) : ℝ) = (Real.sqrt 2 ^ 2 / 16 * ((Real.sqrt 3 + 1) * (Real.sqrt 3 - 1)) : ℝ) := by
    ring_nf
  norm_num [pow_two, pow_succ, h7, h8, h9, h10, h11, h12]
  <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3)]
  all_goals
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  all_goals
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]