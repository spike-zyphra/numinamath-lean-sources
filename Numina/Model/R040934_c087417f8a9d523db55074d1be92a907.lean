import Mathlib

theorem algebra_233259 : (Real.sqrt (6400) + Real.sqrt (6144) + Real.sqrt (4800) + Real.sqrt (4608))^((1 : ℝ)/4) = 1 + Real.sqrt 2 + Real.sqrt 3 := by

  have h1 : Real.sqrt (6400) = 80 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h2 : Real.sqrt (6144) = 32 * Real.sqrt 6 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
    <;> ring_nf <;> norm_num
    <;> ring_nf
  have h3 : Real.sqrt (4800) = 40 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h4 : Real.sqrt (4608) = 48 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h11 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
    <;> ring_nf
  have h6 : (Real.sqrt (6400) + Real.sqrt (6144) + Real.sqrt (4800) + Real.sqrt (4608)) = (1 + Real.sqrt 2 + Real.sqrt 3) ^ 4 := by
    rw [h1, h2, h3, h4]
    have h7 : (32 * Real.sqrt 6) = 32 * (Real.sqrt 2 * Real.sqrt 3) := by
      rw [show Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
        <;> ring_nf
      ]
      <;> ring_nf <;> norm_num
    rw [h7]
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
      sq_nonneg (Real.sqrt 2 - Real.sqrt 3), 
      sq_nonneg (Real.sqrt 2), sq_nonneg (Real.sqrt 3), 
      Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2), 
      Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3), 
      mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3)
    ]
  rw [h6]
  have h10 : ((1 + Real.sqrt 2 + Real.sqrt 3 : ℝ) ^ 4) ^ ((1 : ℝ) / 4) = (1 + Real.sqrt 2 + Real.sqrt 3 : ℝ) := by
    have h11 : ((1 + Real.sqrt 2 + Real.sqrt 3 : ℝ) ^ 4) ^ ((1 : ℝ) / 4) = (1 + Real.sqrt 2 + Real.sqrt 3 : ℝ) := by
      have h12 : ((1 + Real.sqrt 2 + Real.sqrt 3 : ℝ) ^ 4) ^ ((1 : ℝ) / 4) = (1 + Real.sqrt 2 + Real.sqrt 3 : ℝ) := by
        have h13 : ((1 + Real.sqrt 2 + Real.sqrt 3 : ℝ) ^ 4) = (1 + Real.sqrt 2 + Real.sqrt 3) ^ 4 := by ring
        rw [h13]
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals
          have h14 : (1 + Real.sqrt 2 + Real.sqrt 3 : ℝ) ≥ 0 := by
            positivity
          linarith [show (0 : ℝ) ≤ 1 + Real.sqrt 2 + Real.sqrt 3 by positivity]
      linarith
    linarith
  linarith [h10]