import Mathlib

theorem algebra_13593 (t : ℝ) (ht : t > 0) :
    Complex.abs (t + 2 * Real.sqrt 3 * .I) * Complex.abs (6 - 4 * .I) = 26 ↔ t = 1 := by 
  have h1 : Complex.abs (t + 2 * Real.sqrt 3 * Complex.I) = Real.sqrt (t ^ 2 + 12) := by
    simp [Complex.abs, Complex.normSq]
    ring_nf
    <;> rw [show 12 + t ^ 2 = t ^ 2 + 12 by ring]
    all_goals norm_num [Real.sqrt_nonneg]
    all_goals try { norm_num [Real.sqrt_nonneg] }
    all_goals try { ring }
  have h2 : Complex.abs (6 - 4 * Complex.I) = Real.sqrt 52 := by 
    simp [Complex.abs, Complex.normSq]
    ring_nf
    <;> norm_num [Real.sqrt_nonneg, Real.sq_sqrt]
    all_goals try { norm_num [Real.sqrt_nonneg, Real.sq_sqrt] }
    all_goals try { ring }
  have h3 : Complex.abs (6 - 4 * Complex.I) = 2 * Real.sqrt 13 := by
    rw [h2]
    have h4 : Real.sqrt (52 : ℝ) = 2 * Real.sqrt 13 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
      all_goals try { 
        nlinarith [Real.sqrt_nonneg (52 : ℝ), Real.sqrt_nonneg (13 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 52 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by positivity), sq_nonneg (52 : ℝ)]
      }
      all_goals try { 
        norm_num
        <;> nlinarith [Real.sqrt_nonneg (52 : ℝ), Real.sqrt_nonneg (13 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 52 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by positivity)]
      }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg (52 : ℝ), Real.sqrt_nonneg (13 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 52 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by positivity), sq_nonneg (2 * Real.sqrt (13 : ℝ))]
      }
    rw [h4]
    all_goals try { norm_num [Real.sqrt_nonneg, Real.sq_sqrt] }
    all_goals try { ring }
    all_goals try { 
      nlinarith [Real.sqrt_nonneg (52 : ℝ), Real.sqrt_nonneg (13 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 52 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by positivity)]
    }
  rw [h1, h3]
  constructor
  · -- Forward direction: given the equation, prove t = 1
    intro h
    have h4 : Real.sqrt (t ^ 2 + 12) * (2 * Real.sqrt 13) = 26 := by
      simpa using h
    have h5 : Real.sqrt (t ^ 2 + 12) * Real.sqrt 13 = 13 := by
      nlinarith [Real.sqrt_nonneg (t ^ 2 + 12), Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (t ^ 2 + 12) by nlinarith [sq_nonneg t]), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
    have h6 : Real.sqrt (t ^ 2 + 12) ^ 2 = 13 := by
      have h7 : Real.sqrt (t ^ 2 + 12) * Real.sqrt 13 = 13 := h5
      have h8 : Real.sqrt 13 ^ 2 = 13 := by
        rw [Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]
      have h9 : Real.sqrt (t ^ 2 + 12) ^ 2 = 13 := by
        nlinarith [Real.sqrt_nonneg (t ^ 2 + 12), Real.sqrt_nonneg 13]
      linarith
    have h7 : t ^ 2 + 12 = 13 := by
      have h8 : Real.sqrt (t ^ 2 + 12) ^ 2 = t ^ 2 + 12 := by
        rw [Real.sq_sqrt (show (0 : ℝ) ≤ t ^ 2 + 12 by nlinarith [sq_nonneg t])]
      nlinarith [h6, h8]
    have h8 : t ^ 2 = 1 := by
      nlinarith
    have h9 : t = 1 := by
      nlinarith [sq_pos_of_pos ht]
    assumption
  · -- Backward direction: given t = 1, prove the equation
    intro h
    rw [h]
    have h4 : Real.sqrt ((1 : ℝ) ^ 2 + 12) = Real.sqrt 13 := by
      norm_num
    rw [h4]
    have h6 : Real.sqrt 13 * (2 * Real.sqrt 13) = 26 := by
      have h5 : Real.sqrt 13 ^ 2 = 13 := by
        rw [Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]
      nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
    nlinarith [h6, Real.sqrt_nonneg (13 : ℝ)]