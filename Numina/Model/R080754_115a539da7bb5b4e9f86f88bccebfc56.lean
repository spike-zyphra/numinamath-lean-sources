import Mathlib

/- Let $\text{i}$ be the imaginary unit, and the complex number $z=\frac{4+\sqrt{2}\text{i}}{1-\text{i}}$. Then $\left| z \right|$ equals ___          ___. -/
theorem algebra_12605 {z : ℂ} (hz : z = (4 + Real.sqrt 2 * Complex.I) / (1 - Complex.I)) :
    Complex.abs z = 3 := by
  rw [hz]
  have h1 : Complex.abs ((4 + Real.sqrt 2 * Complex.I) / (1 - Complex.I)) =
          Complex.abs (4 + Real.sqrt 2 * Complex.I) / Complex.abs (1 - Complex.I) := by
    field_simp [Complex.abs]
    <;> norm_num [Complex.normSq]
    <;> ring
  rw [h1]
  have h2 : Complex.abs (4 + Real.sqrt 2 * Complex.I) = Real.sqrt 18 := by
    simp [Complex.abs, Complex.normSq]
    ring_nf
    <;> norm_num [Real.sq_sqrt]
    <;> ring_nf <;> norm_num
    all_goals norm_num [Real.sq_sqrt]
  have h3 : Complex.abs (1 - Complex.I) = Real.sqrt 2 := by
    simp [Complex.abs, Complex.normSq]
    ring_nf
    <;> norm_num
    <;> ring_nf <;> norm_num
    all_goals norm_num
  rw [h2, h3]
  have h4 : Real.sqrt 18 / Real.sqrt 2 = 3 := by
    have h4 : Real.sqrt 18 / Real.sqrt 2 = Real.sqrt (18 / 2 : ℝ) := by
      rw [← Real.sqrt_div]
      all_goals norm_num
    rw [h4]
    have h5 : (18 / 2 : ℝ) = 9 := by norm_num
    rw [h5]
    have h5 : Real.sqrt 9 = 3 := by
      rw [Real.sqrt_eq_cases]
      norm_num
    rw [h5]
    all_goals norm_num
  rw [h4]
  all_goals norm_num