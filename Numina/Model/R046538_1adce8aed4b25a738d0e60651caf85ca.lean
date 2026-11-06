import Mathlib

theorem algebra_313301 : (Real.sqrt (5 - Real.sqrt 24)) / (Real.sqrt 10 + 3 - Real.sqrt 6 - Real.sqrt 15) =
    -(1 / 2) * (Real.sqrt 3 + Real.sqrt 5) := by

  have h1 : Real.sqrt 24 = 2 * Real.sqrt 6 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  have h2 : 5 - Real.sqrt 24 = (Real.sqrt 3 - Real.sqrt 2) ^ 2 := by
    rw [h1]
    have h3 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h3]
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 - Real.sqrt 3)]

  have h3 : Real.sqrt (5 - Real.sqrt 24) = Real.sqrt 3 - Real.sqrt 2 := by
    rw [h2]
    have h4 : 0 ≤ Real.sqrt 3 - Real.sqrt 2 := by
      have h5 : Real.sqrt 3 ≥ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
      linarith
    have h7 : Real.sqrt ((Real.sqrt 3 - Real.sqrt 2) ^ 2) = Real.sqrt 3 - Real.sqrt 2 := by
      rw [Real.sqrt_sq]
      linarith [h4]
    rw [h7]

  have h5 : Real.sqrt 10 = Real.sqrt 2 * Real.sqrt 5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  have h6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  have h7 : Real.sqrt 15 = Real.sqrt 3 * Real.sqrt 5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  have h8 : Real.sqrt 10 + 3 - Real.sqrt 6 - Real.sqrt 15 =
    Real.sqrt 2 * Real.sqrt 5 + 3 - (Real.sqrt 2 * Real.sqrt 3) - (Real.sqrt 3 * Real.sqrt 5) := by
    rw [h5, h6, h7]

  rw [h3, h8]

  have h9 : (Real.sqrt 3 - Real.sqrt 2) / (Real.sqrt 2 * Real.sqrt 5 + 3 - (Real.sqrt 2 * Real.sqrt 3) - (Real.sqrt 3 * Real.sqrt 5)) = (Real.sqrt 3 + Real.sqrt 5) / (-2) := by
    field_simp [(show Real.sqrt 2 * Real.sqrt 5 + 3 - (Real.sqrt 2 * Real.sqrt 3) - (Real.sqrt 3 * Real.sqrt 5) ≠ 0 by
      nlinarith [Real.sqrt_pos.mpr (show (0: ℝ) < 2 by norm_num: (0: ℝ) < 2), Real.sqrt_pos.mpr (show (0: ℝ) < 3 by norm_num: (0: ℝ) < 3), Real.sqrt_pos.mpr (show (0: ℝ) < 5 by norm_num: (0: ℝ) < 5), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num: (0 : ℝ) ≤ (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num: (0 : ℝ) ≤ (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num: (0 : ℝ) ≤ (5 : ℝ)), sq_nonneg (Real.sqrt 2 - Real.sqrt 3), sq_nonneg (Real.sqrt 2 - Real.sqrt 5), sq_nonneg (Real.sqrt 3 - Real.sqrt 5)
      ]
    )]
    <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 - Real.sqrt 3), sq_nonneg (Real.sqrt 2 - Real.sqrt 5), sq_nonneg (Real.sqrt 3 - Real.sqrt 5), Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (15 : ℝ) by norm_num)]
  rw [h9]
  ring