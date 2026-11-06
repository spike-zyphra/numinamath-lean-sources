import Mathlib

theorem algebra_10494 (t : ℝ) (A B : ℝ × ℝ)
    (hA : A = (t - 4, -1)) (hB : B = (-2, t + 3))
    (h : (midpoint ℝ A B - A).1^2 + (midpoint ℝ A B - A).2^2 = t^2 / 2) :
    t = -5 := by 
  rw [hA, hB] at h 
  simp [midpoint_eq_smul_add, Prod.ext_iff, smul_add, add_mul, mul_add, mul_comm, mul_assoc] at h 
  ring_nf at h 
  nlinarith