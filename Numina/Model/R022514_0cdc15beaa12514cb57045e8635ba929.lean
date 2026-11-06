import Mathlib

theorem algebra_204512 {f g : Polynomial ℝ} (hfg : ∀ x : ℝ, (1 + Complex.I * x) ^ 2 ^ 201 = f.eval x / (Complex.I * g.eval x)) :
    ∑ coeff in f.coeffs, coeff = 2 ^ 1000 := by
  have eq1 := hfg 0
  have eq2 := hfg 1
  simp [pow_mul, pow_zero, Complex.ext_iff, Complex.I_mul_I, Complex.div_re, Complex.div_im, Complex.normSq] at eq1 eq2
  all_goals 
    nlinarith