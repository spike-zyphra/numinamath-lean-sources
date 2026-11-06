import Mathlib

theorem inequalities_605327 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (_ : 0 < z)
    (h1 : x ≤ 2) (h2 : y ≤ 3) (h3 : x + y + z = 11) :
    Real.sqrt (x * y * z) ≤ 6 := by
  have h4 : x * y * z ≤ 36 := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 3), sq_nonneg (z - 6),
              mul_nonneg (show (0 : ℝ) ≤ 2 - x by linarith) (show (0 : ℝ) ≤ 3 - y by linarith),
              mul_pos hx hy, mul_pos hx (show 0 < z by linarith),
              mul_pos hy (show 0 < z by linarith)]
  have h5 : Real.sqrt (x * y * z) ≤ Real.sqrt (36 : ℝ) := Real.sqrt_le_sqrt (by nlinarith)
  have h6 : Real.sqrt (36 : ℝ) = 6 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h6] at h5
  linarith