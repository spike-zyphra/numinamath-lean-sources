import Mathlib

theorem algebra_11219 (A B C : ℝ × ℝ)
    (hA : A = (1, 2)) (hB : B = (1, 8)) (hC : C = (5, 5)) :
    Real.sqrt ((B.1 - A.1)^2 + (B.2 - A.2)^2) +
    Real.sqrt ((C.1 - B.1)^2 + (C.2 - B.2)^2) +
    Real.sqrt ((C.1 - A.1)^2 + (C.2 - A.2)^2) = 16 := by
  have h1 : Real.sqrt ((B.1 - A.1)^2 + (B.2 - A.2)^2) = 6 := by
    rw [hA, hB]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h2 : Real.sqrt ((C.1 - B.1)^2 + (C.2 - B.2)^2) = 5 := by
    rw [hB, hC]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h3 : Real.sqrt ((C.1 - A.1)^2 + (C.2 - A.2)^2) = 5 := by
    rw [hA, hC]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h1, h2, h3]
  all_goals norm_num