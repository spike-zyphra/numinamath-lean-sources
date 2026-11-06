import Mathlib
open Real

/- The discriminant of the equation x² + 2x√3 + 3 = 0 is zero. Hence, its roots are:
(A) real and equal (B) rational and equal  (C) rational and unequal
(D) irrational and unequal  (E) imaginary -/
theorem algebra_95797 (x : ℝ) (h : x^2 + 2 * x * Real.sqrt 3 + 3 = 0) :
x = -Real.sqrt 3 ∧ Irrational x := by
  -- solve x
  have hx:x = -Real.sqrt 3 := by
    rw [pow_two,← one_mul (x*x),mul_comm _ √3,← mul_assoc _ 2 _] at h
    have h3 : (√3 * 2)^2=12:=by rw [mul_pow];simp;norm_num
    rw [quadratic_eq_zero_iff (by simp) (by unfold discrim;rw [h3];norm_num:discrim (1:ℝ) (√3 * 2) 3 = 0 * 0)] at h
    simp at h
    linarith
    -- linarith [Real.sq_sqrt (show 0 ≤ 3 by norm_num)]
  constructor
  · exact hx
  -- prove that √3 is irrational
  · rw [hx,(by simp:-√3=↑(-1:ℤ)*√3)]
    apply Irrational.int_mul _
    · linarith
    · simpa using Nat.prime_three.irrational_sqrt