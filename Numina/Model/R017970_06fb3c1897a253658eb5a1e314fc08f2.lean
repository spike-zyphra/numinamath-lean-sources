import Mathlib

theorem algebra_324419 (z : ℂ) (h : ∃ α : ℝ, α^2 + z * α + z * .I = 0) :
    (z.re)^2 * (1 - z.im) = z.im^3 := by
  rcases h with ⟨α, hα⟩
  have eq1 := congr_arg Complex.re hα
  have eq2 := congr_arg Complex.im hα
  simp [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im] at eq1 eq2
  have eq3 : (z.re : ℝ) = - (z.im : ℝ) * α := by 
    nlinarith 
  have eq4 : α^2 + (z.re : ℝ) * α - (z.im : ℝ) = 0 := by 
    nlinarith
  rw [eq3] at eq4 
  have eq5 : α^2 * (1 - (z.im : ℝ)) = (z.im : ℝ) := by
    nlinarith
  have eq6 : (z.re : ℝ)^2 = (z.im : ℝ)^2 * α^2 := by 
    have h1 : (z.re : ℝ) = - (z.im : ℝ) * α := eq3
    rw [h1]
    nlinarith
  calc 
    (z.re : ℝ)^2 * (1 - (z.im : ℝ)) = (z.im : ℝ)^2 * α^2 * (1 - (z.im : ℝ)) := by
      rw [eq6]
    _ = (z.im : ℝ)^2 * (z.im : ℝ) := by 
      have h : α^2 * (1 - (z.im : ℝ)) = (z.im : ℝ) := eq5
      nlinarith [sq_nonneg (α), sq_nonneg (z.im : ℝ)]
    _ = (z.im : ℝ)^3 := by 
      ring