import Mathlib

open Real

theorem inequalities_195899 (a b c x y z : ℝ) (ha : a = x + y + sqrt (x * y))
    (hb : b = y + z + sqrt (y * z)) (hc : c = z + x + sqrt (z * x)) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    a + b + sqrt (a * b) > c := by
  have hxy : 0 < x * y := mul_pos hx hy
  have hyz : 0 < y * z := mul_pos hy hz
  have hzx : 0 < z * x := mul_pos hz hx
  have ha2 : 0 < a := by
    rw [ha]
    nlinarith [Real.sqrt_nonneg (x * y), Real.sq_sqrt (show 0 ≤ (x * y : ℝ) by positivity)]
  have hb2 : 0 < b := by
    rw [hb]
    nlinarith [Real.sqrt_nonneg (y * z), Real.sq_sqrt (show 0 ≤ (y * z : ℝ) by positivity)]
  have hc2 : 0 < c := by
    rw [hc]
    nlinarith [Real.sqrt_nonneg (z * x), Real.sq_sqrt (show 0 ≤ (z * x : ℝ) by positivity)]
  have h9 : 0 < a * b := mul_pos ha2 hb2
  have h12 : a + b + sqrt (a * b) - c > 0 := by
    have h7a : 0 < x * y := mul_pos hx hy
    have h7b : 0 < y * z := mul_pos hy hz
    have h7c : 0 < z * x := mul_pos hz hx
    have h8a : 0 < a := by
      rw [ha]
      nlinarith [Real.sqrt_nonneg (x * y), Real.sq_sqrt (show 0 ≤ (x * y : ℝ) by positivity)]
    have h8b : 0 < b := by
      rw [hb]
      nlinarith [Real.sqrt_nonneg (y * z), Real.sq_sqrt (show 0 ≤ (y * z : ℝ) by positivity)]
    have h8c : 0 < c := by
      rw [hc]
      nlinarith [Real.sqrt_nonneg (z * x), Real.sq_sqrt (show 0 ≤ (z * x : ℝ) by positivity)]
    have h9 : 0 < a * b := mul_pos h8a h8b
    have h9a : sqrt (a * b) ≥ 0 := Real.sqrt_nonneg (a * b)
    -- complex inequality
    nlinarith [Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (x * y), Real.sqrt_nonneg (y * z), Real.sqrt_nonneg (z * x),
      Real.sq_sqrt (show 0 ≤ (a * b : ℝ) by positivity),
      Real.sq_sqrt (show 0 ≤ (x * y : ℝ) by positivity), Real.sq_sqrt (show 0 ≤ (y * z : ℝ) by positivity), Real.sq_sqrt (show 0 ≤ (z * x : ℝ) by positivity),
      sq_nonneg (sqrt (x * y) - sqrt (y * z)), sq_nonneg (sqrt (y * z) - sqrt (z * x)), sq_nonneg (sqrt (x * y) - sqrt (z * x)),
      mul_nonneg (Real.sqrt_nonneg (x * y)) (Real.sqrt_nonneg (y * z)), mul_nonneg (Real.sqrt_nonneg (y * z)) (Real.sqrt_nonneg (z * x)), mul_nonneg (Real.sqrt_nonneg (x * y)) (Real.sqrt_nonneg (z * x))
    ]
  linarith