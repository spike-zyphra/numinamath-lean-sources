import Mathlib

theorem inequalities_597087 (x y a : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y = 2 * a) :
    x ^ 3 * y ^ 3 * (x ^ 2 + y ^ 2) ^ 2 ≤ 4 * a ^ 10 := by
  have h1 : 0 ≤ x * y := by 
    nlinarith
  have h2 : x * y ≤ a ^ 2 := by 
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2 * a)]
  have h3 : x ^ 2 + y ^ 2 = 4 * a ^ 2 - 2 * (x * y) := by
    have h4 : x + y = 2 * a := hxy 
    have h5 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by
      nlinarith
    rw [h4] at h5 
    linarith
  have h4 : x ^ 3 * y ^ 3 = (x * y) ^ 3 := by 
    ring

  rw [h4, h3]
  nlinarith [sq_nonneg ((x * y) ^ 2 - a ^ 4), sq_nonneg ((x * y) - a ^ 2), sq_nonneg ((x * y) * (x * y - a ^ 2)), sq_nonneg (x * y), sq_nonneg (x * y - a ^ 2), sq_nonneg ((4 * a ^ 2 - 2 * (x * y)) - 2 * a ^ 2), sq_nonneg ((x - y) ), sq_nonneg (x * (x - a)), sq_nonneg (y * (y - a)), sq_nonneg (x * (y - a)), sq_nonneg (y * (x - a)), mul_pos hx hy, mul_pos (show 0 < x by linarith) (show 0 < y by linarith), pow_two_nonneg (x - y), mul_nonneg (show 0 ≤ x by nlinarith) (show 0 ≤ y by nlinarith), sq_nonneg (x * y - a ^ 2), sq_nonneg (x * y * (x * y)), sq_nonneg ( (x * y) ^ 2 - a ^ 2 * (x * y) ) ]