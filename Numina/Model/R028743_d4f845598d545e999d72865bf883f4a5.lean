import Mathlib

/- Given that $A$ and $B$ are points on ${{C}_{1}}$: ${{x}^{2}}-y+1=0$ and ${{C}_{2}}$: ${{y}^{2}}-x+1=0$ respectively, then the minimum value of $\left| AB \right|$ is ___          ___. -/
theorem algebra_11366 (A B : ℝ × ℝ)
    (hA : A.1^2 - A.2 + 1 = 0) (hB : B.2^2 - B.1 + 1 = 0) :
    Real.sqrt ((A.1 - B.1)^2 + (A.2 - B.2)^2) ≥ 3 * Real.sqrt 2 / 4 := by
  have hA2 : A.2 = A.1^2 + 1 := by linarith
  have hB1 : B.1 = B.2^2 + 1 := by linarith
  have h1 : (A.1 - B.1)^2 + (A.2 - B.2)^2 = (A.1 - (B.2^2 + 1))^2 + ((A.1^2 + 1) - B.2)^2 := by
    rw [hA2, hB1]
    <;> ring_nf
  have h2 : (A.1 - (B.2^2 + 1))^2 + ((A.1^2 + 1) - B.2)^2 ≥ 9 / 8 := by 
    nlinarith [sq_nonneg (A.1 - 1 / 2), sq_nonneg (B.2 - 1 / 2), 
      sq_nonneg (A.1 - B.2), sq_nonneg (A.1 + B.2 - 1), sq_nonneg (A.1 - B.2^2), sq_nonneg (B.2 - A.1^2), 
      sq_nonneg (A.1^2 - B.2^2), sq_nonneg (A.1 * B.2 - 1 / 4)]
  have h3 : (A.1 - B.1)^2 + (A.2 - B.2)^2 ≥ 9 / 8 := by
    nlinarith [h1, h2]
  have h4 : Real.sqrt ((A.1 - B.1)^2 + (A.2 - B.2)^2) ≥ Real.sqrt (9 / 8) := Real.sqrt_le_sqrt (by linarith [h3])
  have h5 : Real.sqrt (9 / 8) = 3 * Real.sqrt 2 / 4 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num [mul_add, pow_two]
    <;> ring_nf <;> norm_num
  linarith [h4, h5]