import Mathlib

/- If the eccentricity of the hyperbola $\Gamma_{1}: \frac{x^{2}}{a^{2}}- \frac{y^{2}}{b^{2}}=1(a$, $b>0)$ is $3$, then the eccentricity of the hyperbola $\Gamma_{2}: \frac{y^{2}}{b^{2}}- \frac{x^{2}}{a^{2}}=1$ is ___          ___. -/
theorem algebra_8548 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : √(1 + b^2 / a^2) = 3) :
    √(1 + a^2 / b^2) = 3 * √2 / 4 := by 
  have h1 : 1 + b ^ 2 / a ^ 2 = 9 := by
    calc
      1 + b ^ 2 / a ^ 2 = (√(1 + b ^ 2 / a ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = 3 ^ 2 := by rw [h]
      _ = 9 := by norm_num
  have h2 : b ^ 2 = 8 * a ^ 2 := by 
    field_simp [ha.ne.symm] at h1 ⊢
    nlinarith
  have h3 : a ^ 2 / b ^ 2 = 1 / 8 := by 
    rw [show b ^ 2 = 8 * a ^ 2 by linarith [h2]]
    field_simp [ha.ne.symm]
    <;> nlinarith
  have h4 : 1 + a ^ 2 / b ^ 2 = 9 / 8 := by 
    rw [h3]
    <;> field_simp <;> ring
  calc
    √(1 + a^2 / b^2) = √(9 / 8) := by rw [h4]
    _ = 3 * √2 / 4 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
      <;> ring_nf <;> norm_num