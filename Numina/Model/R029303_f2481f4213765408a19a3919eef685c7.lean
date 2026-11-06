import Mathlib

theorem algebra_9201 {z : ℂ} (hz : ∃ r : ℝ, z + 2 * .I = r) (hz' : ∃ r : ℝ, z / (2 - .I) = r) :
    Complex.abs z = 2 * Real.sqrt 5 := by

  rcases hz with ⟨r, hr⟩
  rcases hz' with ⟨s, hs⟩

  have h1 : z.im = -2 := by 
    have eq1 := congr_arg Complex.im hr
    simp [Complex.add_im] at eq1 
    linarith

  have eq1 := congr_arg Complex.re hs
  have eq2 := congr_arg Complex.im hs
  have eq4 : z.re = 4 := by
    simp [Complex.div_re, Complex.div_im, Complex.normSq, h1] at eq1 eq2 
    ring_nf at eq1 eq2 
    nlinarith 

  have h4 : Complex.abs z = Real.sqrt ((z.re) ^ 2 + (z.im) ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf 
  rw [h4, eq4, h1]
  have h5 : Real.sqrt ((4: ℝ) ^ 2 + (-2: ℝ) ^ 2) = Real.sqrt (20: ℝ) := by
    norm_num 
  rw [h5]
  have h8 : Real.sqrt (20: ℝ) = 2 * Real.sqrt 5 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  rw [h8]
  all_goals norm_num