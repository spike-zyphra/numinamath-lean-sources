import Mathlib

theorem algebra_21329 (A B : ℝ × ℝ)
    (hA : A = (0, 0)) (hB : B = (3, 4)) :
    Real.sqrt ((B.1 - A.1)^2 + (B.2 - A.2)^2) = 5 := by
  rw [hA, hB]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num