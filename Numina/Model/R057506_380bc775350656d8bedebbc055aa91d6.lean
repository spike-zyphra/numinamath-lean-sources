import Mathlib

theorem algebra_299440 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : 2 * x - 3 * Real.sqrt (x * y) - 2 * y = 0) :
    (x ^ 2 + 4 * x * y - 16 * y ^ 2) / (2 * x ^ 2 + x * y - 9 * y ^ 2) = 16 / 27 := by
  have h1 : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y := by
    rw [Real.sqrt_mul (by positivity)]
  have h2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith)
  have h3 : Real.sqrt y ^ 2 = y := Real.sq_sqrt (show 0 ≤ (y : ℝ) by linarith)
  have h4 : 2 * Real.sqrt x ^ 2 - 3 * (Real.sqrt x * Real.sqrt y) - 2 * Real.sqrt y ^ 2 = 0 := by
    rw [h1] at h
    nlinarith [Real.sqrt_nonneg (x * y), Real.sqrt_nonneg (x), Real.sqrt_nonneg (y), h2, h3, h]

  have h5 : (2 * Real.sqrt x + Real.sqrt y) * (Real.sqrt x - 2 * Real.sqrt y) = 0 := by
    nlinarith [h4, Real.sqrt_nonneg (x), Real.sqrt_nonneg (y), h2, h3]

  cases' (mul_eq_zero.mp h5) with h6 h7

  · -- Case where 2 * sqrt(x) + sqrt(y) = 0, which is impossible
    have h61 : Real.sqrt x ≥ 0 := Real.sqrt_nonneg x
    have h62 : Real.sqrt y ≥ 0 := Real.sqrt_nonneg y
    have h63 : 2 * Real.sqrt x + Real.sqrt y > 0 := by
      nlinarith [Real.sqrt_pos.2 hx, Real.sqrt_pos.2 hy, h61, h62]
    nlinarith

  · -- Case where sqrt(x) - 2 * sqrt(y) = 0, so sqrt(x) = 2 * sqrt(y)
    have h8 : Real.sqrt x = 2 * Real.sqrt y := by linarith
    have h9 : x = 4 * y := by
      calc
        x = Real.sqrt x ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = (2 * Real.sqrt y) ^ 2 := by rw [h8]
        _ = 4 * (Real.sqrt y ^ 2) := by ring
        _ = 4 * y := by rw [Real.sq_sqrt (show 0 ≤ (y : ℝ) by linarith)]
    have h10 : x ^ 2 + 4 * x * y - 16 * y ^ 2 = 16 * y ^ 2 := by
      rw [show x = 4 * y by linarith]
      ring_nf
    have h11 : 2 * x ^ 2 + x * y - 9 * y ^ 2 = 27 * y ^ 2 := by
      rw [show x = 4 * y by linarith]
      ring_nf
    have h12 : (x ^ 2 + 4 * x * y - 16 * y ^ 2) / (2 * x ^ 2 + x * y - 9 * y ^ 2) = (16 * y ^ 2) / (27 * y ^ 2) := by
      rw [h10, h11]
    rw [h12]
    have h13 : y ^ 2 > 0 := by nlinarith [hy]
    field_simp [h13]
    <;> nlinarith