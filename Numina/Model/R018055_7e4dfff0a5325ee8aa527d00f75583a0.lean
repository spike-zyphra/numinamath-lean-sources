import Mathlib

theorem number_theory_302965 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hord : a < b ∧ b < c) (hdiv : a * b * c ∣ (a * b - 1) * (b * c - 1) * (c * a - 1)) :
    ∃ x y z, x > 0 ∧ y > 0 ∧ z > 0 ∧ x + y > z ∧ y + z > x ∧ z + x > y ∧
    (1 / 2) * x * y * z = Real.sqrt 6 / 2 := by 
  use (1 : ℝ)
  use Real.sqrt 2
  use Real.sqrt 3
  constructor
  · -- Show x > 0
    norm_num
  constructor
  · -- Show y > 0
    positivity
  constructor
  · -- Show z > 0
    positivity
  constructor
  · -- Show x + y > z
    have h2 : (1 + Real.sqrt 2) ^ 2 > (Real.sqrt 3) ^ 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 - Real.sqrt 3), Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), sq_nonneg (1 + Real.sqrt 2 - Real.sqrt 3)]
  constructor
  · -- Show y + z > x
    have h3 : Real.sqrt 2 + Real.sqrt 3 > 1 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 - 1), sq_nonneg (Real.sqrt 3 - 1)]
    linarith
  constructor
  · -- Show z + x > y
    have h4 : Real.sqrt 3 + (1 : ℝ) > Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 3 - Real.sqrt 2), sq_nonneg (Real.sqrt 3 - 1)]
    linarith
  · -- Show (1 / 2) * x * y * z = √6 / 2
    have h5 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
      rw [← Real.sqrt_mul (by norm_num)]
      norm_num
    field_simp
    <;> nlinarith [Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), h5]
    <;> linarith