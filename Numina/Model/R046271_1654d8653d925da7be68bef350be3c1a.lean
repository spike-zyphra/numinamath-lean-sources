import Mathlib

theorem algebra_1800 {A B : ℝ} (hA : A > 0) (hB : B > 0)
    (ha : 20 = A * Real.exp (B * 3)) (hb : 200 = A * Real.exp (B * 6)) :
    A = 2 := by 
  have h1 : A * Real.exp (B * 3) = 20 := by linarith
  have h2 : A * Real.exp (B * 6) = 200 := by linarith
  have h3 : Real.exp (B * 6) = (Real.exp (B * 3)) ^ 2 := by
    have h4 : B * 6 = 2 * (B * 3) := by ring
    rw [h4]
    have h5 : Real.exp (2 * (B * 3)) = (Real.exp (B * 3)) ^ 2 := by
      rw [← Real.exp_nat_mul]
      ring_nf
      <;> norm_num [Real.exp_zero]
    exact h5
  rw [h3] at h2
  have h6 : Real.exp (B * 3) = 10 := by
    nlinarith [h1, h2, Real.exp_pos (B * 3), Real.exp_pos (B * 6), mul_pos hA (Real.exp_pos (B * 3)), mul_pos hA (Real.exp_pos (B * 6))]
  nlinarith [h1, h6, mul_pos hA (Real.exp_pos (B * 3)), Real.exp_pos (B * 3)]