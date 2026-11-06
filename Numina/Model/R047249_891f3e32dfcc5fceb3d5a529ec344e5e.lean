import Mathlib

theorem algebra_15447 {a b : ℤ} (ha : a > 0) (hb : b > 0)
    (h : (a - b * Complex.I)^2 = 8 - 6 * Complex.I) :
    a - b * Complex.I = 3 - Complex.I := by
  have eq1 := congr_arg Complex.re h
  have eq2 := congr_arg Complex.im h
  simp [pow_two, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eq1 eq2
  have eq3 : (a : ℝ) * (a : ℝ) - (b : ℝ) * (b : ℝ) = (8 : ℝ) := by
    ring_nf at eq1 ⊢
    linarith
  have eq4 : -2 * ((a : ℝ) * (b : ℝ)) = (-6 : ℝ) := by
    have h1 : ((b : ℝ) * (a : ℝ)) = ((a : ℝ) * (b : ℝ)) := by ring
    rw [h1] at eq2
    linarith
  have eq5 : (a * b : ℝ) = (3 : ℝ) := by
    nlinarith
  have eq6 : a * b = 3 := by
    exact_mod_cast eq5
  have eq7 : a^2 - b^2 = 8 := by
    have eq8 : (a : ℝ)^2 - (b : ℝ)^2 = (8 : ℝ) := by
      nlinarith
    have eq9 : (a^2 - b^2 : ℝ) = (8 : ℝ) := by
      ring_nf at eq8 ⊢
      nlinarith
    have eq10 : (a^2 - b^2 : ℤ) = (8 : ℤ) := by
      exact_mod_cast eq9
    linarith
  have h4 : a = 3 := by
    have h1 : a ≤ 3 := by
      have h4 : a ∣ 3 := by
        use b
        all_goals linarith
      have h5 : a ≤ 3 := by
        exact Int.le_of_dvd (by norm_num) h4
      linarith
    interval_cases a <;> try { 
      omega 
    }
    <;> try { 
      have h8 : b ≤ 3 := by nlinarith 
      interval_cases b 
      <;> omega 
    }
  have h5 : b = 1 := by
    rw [show a = 3 by linarith] at eq6
    nlinarith
  rw [show (a : ℤ) = 3 by linarith, show (b : ℤ) = 1 by linarith]
  all_goals
    simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    all_goals norm_num
    all_goals nlinarith
  all_goals norm_num
  all_goals nlinarith