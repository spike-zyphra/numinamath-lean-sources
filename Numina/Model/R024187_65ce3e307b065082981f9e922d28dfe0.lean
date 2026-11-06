import Mathlib.Tactic

open Real

theorem inequalities_148469 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x^4 + y^4 + z^2 ≥ x * y * z * sqrt 8 := by

  have h1 : x^4 + y^4 ≥ 2 * x^2 * y^2 := by
    nlinarith [sq_nonneg (x^2 - y^2)]

  have h2 : 2 * x^2 * y^2 + z^2 ≥ x * y * z * sqrt 8 := by
    have h3 : (sqrt 8 : ℝ) = 2 * sqrt 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num [mul_add, mul_assoc]
      <;> linarith
    rw [h3]
    nlinarith [sq_nonneg (2 * x * y - z * Real.sqrt 2 / 2), sq_nonneg (z * Real.sqrt 2 - 2 * x * y), sq_nonneg (z - Real.sqrt 2 * (x * y)), 
      Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
      Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
    ]
  
  have h3 : x^4 + y^4 + z^2 ≥ 2 * x^2 * y^2 + z^2 := by
    linarith [h1]

  linarith [h3, h2]