import Mathlib

open Complex

theorem algebra_98574 (a b c d : ℝ) (m n : ℕ) (_ : m > 0) (hn : n > 0)
    (h1 : (-20)^3 + a * (-20) + b = 0) (h2 : (-21)^3 + c * (-21)^2 + d = 0)
    (h3 : (m+ √n * Complex.I)^3 + a * (m + √n * Complex.I) + b = 0)
    (h4 : (m + √n * Complex.I)^3 + c * (m + √n * Complex.I)^2 + d = 0) :
    m + n = 330 := by
  have eq1 := congr_arg Complex.re h3
  have eq2 := congr_arg Complex.im h3
  have eq3 := congr_arg Complex.re h4
  have eq4 := congr_arg Complex.im h4
  simp [pow_three, pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, 
      Complex.I_re, Complex.I_im, mul_add, mul_assoc] at eq1 eq2 eq3 eq4
  ring_nf at eq1 eq2 eq3 eq4
  have hn1 : Real.sqrt (↑n : ℝ) > 0 := by
    have h5 : (Real.sqrt (↑n : ℝ)) > 0 := by
      apply Real.sqrt_pos.2
      have hn0 : (↑n : ℝ) > (0 : ℝ) := by
        exact_mod_cast show (n : ℝ) > (0 : ℝ) by exact_mod_cast hn
      nlinarith
    linarith
  have h6 : (3 * (↑m : ℝ) ^ 2 - (↑n : ℝ)) + (a : ℝ) = 0 := by 
    nlinarith
  have h8 : (3 * (↑m : ℝ) ^ 2 - (↑n : ℝ)) + 2 * (↑m : ℝ) * (c : ℝ) = 0 := by 
    nlinarith
  have hm : (↑m : ℝ) = 10 := by
    nlinarith [sq_nonneg ( (↑n : ℝ) - 320 ), Real.sqrt_nonneg (↑n : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (↑n : ℝ) by nlinarith), sq_nonneg ((↑m : ℝ) - 10), Real.sqrt_nonneg (↑n : ℝ)]
  have hn2 : (↑n : ℝ) = 320 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (↑n : ℝ) by nlinarith), Real.sqrt_nonneg (↑n : ℝ)]
  have hm11 : m = 10 := by
    exact_mod_cast hm
  have hn11 : n = 320 := by
    exact_mod_cast hn2
  omega