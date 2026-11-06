import Mathlib

theorem algebra_16643 (A B : ℝ × ℝ)
    (hA : A = (0, 0))
    (hB : B = (20 - 60, 10 - 40)) :
    Real.sqrt ((B.1 - A.1)^2 + (B.2 - A.2)^2) = 50 := by
  rw [hA, hB]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  <;> ring_nf <;> norm_num