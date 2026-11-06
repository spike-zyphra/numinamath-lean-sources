import Mathlib

/- If ${{x}_{1}}=1$, ${{x}_{2}}=1-\text{i}$, ${{x}_{3}}=1+\text{i}$ (where $\text{i}$ is the imaginary unit) are the three solutions of the equation ${{x}^{3}}+a{{x}^{2}}+bx+c=0$, then $a+b-c=$ ___          ___. -/
theorem algebra_10407 {a b c : ℝ} (x1 x2 x3 : ℂ) (hx1 : x1 = 1) (hx2 : x2 = 1 - Complex.I)
    (hx3 : x3 = 1 + Complex.I) (h : x1^3 + a * x1^2 + b * x1 + c = 0 ∧
    x2^3 + a * x2^2 + b * x2 + c = 0 ∧ x3^3 + a * x3^2 + b * x3 + c = 0) :
    a + b - c = 3 := by
  rcases h with ⟨h1, h2, h3⟩
  rw [hx1] at h1
  rw [hx2] at h2
  rw [hx3] at h3
  have eq1 := congr_arg (fun z => z.re) h1
  have eq2 := congr_arg (fun z => z.im) h1
  simp [pow_two, pow_three, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eq1 eq2
  have eq3 := congr_arg (fun z => z.re) h2
  have eq4 := congr_arg (fun z => z.im) h2
  simp [pow_two, pow_three, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eq3 eq4
  have eq5 := congr_arg (fun z => z.re) h3
  have eq6 := congr_arg (fun z => z.im) h3
  simp [pow_two, pow_three, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eq5 eq6
  linarith