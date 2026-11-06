import Mathlib

theorem algebra_10656 {m : ℝ} (h : ∃! x : ℝ, x^2 + (1 - 2 * Complex.I) * x + 3 * m - Complex.I = 0) :
    (-(1 / 2) + 2 * Complex.I) ∈ {x | x^2 + (1 - 2 * Complex.I) * x + 3 * m - Complex.I = 0} := by 
  rcases h with ⟨x, h_eq, h_Unique⟩
  have h_eq' : (x : ℝ)^2 + (1 - 2 * Complex.I) * (x : ℝ) + 3 * m - Complex.I = 0 := h_eq
  have eq1 := congr_arg Complex.re h_eq'
  have eq2 := congr_arg Complex.im h_eq'
  simp [pow_two, Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re, Complex.I_im] at eq1 eq2
  have hx1 : x = -1/2 := by
    nlinarith
  have hm : m = 1/12 := by
    rw [hx1] at eq1
    nlinarith
  simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re, Complex.I_im, hm]
  all_goals norm_num
  <;> nlinarith