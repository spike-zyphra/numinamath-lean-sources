import Mathlib

theorem algebra_13144 {a b : ℝ} (ha : a ≠ 0) (h : a * (-2 - 3 * Complex.I)^3 + 3 * (-2 - 3 * Complex.I)^2 + b * (-2 - 3 * Complex.I) - 65 = 0) :
    ∃ x : ℝ, a * x^3 + 3 * x^2 + b * x - 65 = 0 ∧ x = 5 / 2 := by
  have eq1 := congr_arg Complex.re h
  have eq2 := congr_arg Complex.im h
  simp [pow_two, pow_three, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_add, mul_comm, mul_assoc] at eq1 eq2
  ring_nf at eq1 eq2 
  have eq3 : -9 * a + 36 - 3 * b = 0 := by
    nlinarith
  have eq4 : 46 * a - 2 * b = 80 := by
    nlinarith
  have h4 : a = 2 := by
    have eq5 : b = 12 - 3 * a := by
      linarith
    rw [eq5] at eq4
    linarith
  have hb : b = 6 := by
    rw [h4] at eq3 eq4
    nlinarith
  use 5 / 2
  constructor
  · -- Show that $5/2$ is a root 
    rw [h4, hb]
    norm_num 
  · -- Trivial equality 
    rfl