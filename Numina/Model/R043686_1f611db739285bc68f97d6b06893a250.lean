import Mathlib

open Real

theorem inequalities_220543 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    sqrt (x / 2) + sqrt (y / 2) ≤ sqrt (x + y) := by
  have h1 : (sqrt (x / 2) + sqrt (y / 2)) ^ 2 ≤ (sqrt (x + y)) ^ 2 := by
    have h2 : (sqrt (x / 2) + sqrt (y / 2)) ^ 2 = (sqrt (x / 2)) ^ 2 + (sqrt (y / 2)) ^ 2 + 2 * (sqrt (x / 2) * sqrt (y / 2)) := by ring
    have h3 : (sqrt (x / 2)) ^ 2 = x / 2 := by
      rw [Real.sq_sqrt]
      linarith
    have h4 : (sqrt (y / 2)) ^ 2 = y / 2 := by
      rw [Real.sq_sqrt]
      linarith
    have h5 : sqrt (x / 2) * sqrt (y / 2) = Real.sqrt ((x / 2) * (y / 2)) := by
      rw [← Real.sqrt_mul (by linarith)]
    have h6 : (x / 2) * (y / 2) = (x * y) / 4 := by ring
    have h7 : Real.sqrt ((x / 2) * (y / 2)) = Real.sqrt ((x * y) / 4) := by
      rw [h6]
    have h8 : Real.sqrt ((x * y) / 4) = Real.sqrt (x * y) / 2 := by
      have h9 : Real.sqrt ((x * y) / 4) = Real.sqrt ((x * y) / (2 ^ 2)) := by
        ring_nf
      rw [h9]
      have h10 : Real.sqrt ((x * y) / (2 ^ 2)) = Real.sqrt (x * y) / Real.sqrt (2 ^ 2) := by
        field_simp [Real.sqrt_div]
      rw [h10]
      have h11 : Real.sqrt (2 ^ 2) = 2 := by
        rw [Real.sqrt_sq (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      rw [h11]
    have h9 : (sqrt (x / 2) + sqrt (y / 2)) ^ 2 = (x + y) / 2 + Real.sqrt (x * y) := by
      rw [h2, h3, h4, h5, h7, h8]
      <;> ring_nf
    have h11 : (sqrt (x + y)) ^ 2 = x + y := by
      apply Real.sq_sqrt
      linarith
    have h12 : (x + y) / 2 + Real.sqrt (x * y) ≤ x + y := by
      nlinarith [Real.sqrt_nonneg (x * y), Real.sq_sqrt (show 0 ≤ x * y by nlinarith), sq_nonneg (sqrt (x) - sqrt (y)), mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y), sq_nonneg (x - y)]
    rw [h9, h11]
    linarith [h12]
  have h2 : 0 ≤ sqrt (x / 2) + sqrt (y / 2) := by
    apply add_nonneg
    · apply Real.sqrt_nonneg
    · apply Real.sqrt_nonneg
  have h3 : 0 ≤ sqrt (x + y) := Real.sqrt_nonneg (x + y)
  nlinarith [Real.sqrt_nonneg (x / 2), Real.sqrt_nonneg (y / 2), Real.sqrt_nonneg (x + y), h1, sq_nonneg (sqrt (x / 2) + sqrt (y / 2) - sqrt (x + y))]