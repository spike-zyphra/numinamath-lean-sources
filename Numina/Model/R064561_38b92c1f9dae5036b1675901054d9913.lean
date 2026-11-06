import Mathlib

theorem algebra_19521 (A B : ℝ × ℝ) (hA : A = (1, -2)) (hB : B = (-4, 10)) :
    Real.sqrt ((A.1 - B.1)^2 + (A.2 - B.2)^2) * 4 = 52 := by 
  rw [hA, hB]
  have h1 : Real.sqrt ((1 - -4:ℝ)^2 + (-2 - 10:ℝ)^2) = 13 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> linarith
  rw [h1]
  all_goals norm_num