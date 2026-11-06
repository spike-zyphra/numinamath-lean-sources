import Mathlib

theorem algebra_138070 (a b c : ℤ) (_ : 0 < a) (h₀ : 0 < b) (h₁ : 0 < c)
    (h₂ : c = (a + Complex.I * b)^3 - 107 * Complex.I) :
    c = 198 := by
  have eq1 := congr_arg Complex.re h₂
  have eq2 := congr_arg Complex.im h₂
  simp [pow_three, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, 
      Complex.ofReal_re, Complex.ofReal_im] at eq1 eq2
  ring_nf at eq1 eq2
  have eq3 : (3 * a ^ 2 * b - b ^ 3 : ℝ) = (107 : ℝ) := by
    nlinarith
  have eq4 : (3 * a ^ 2 * b - b ^ 3 : ℤ) = 107 := by
    exact_mod_cast eq3
  have eq5 : c = a ^ 3 - 3 * a * b ^ 2 := by
    have h : (c : ℝ) = (a ^ 3 - 3 * a * b ^ 2 : ℝ) := by
      linarith
    exact_mod_cast h
  have eq6 : b * (3 * a ^ 2 - b ^ 2) = 107 := by
    nlinarith
  have h3 : b ∣ 107 := by
    use (3 * a ^ 2 - b ^ 2)
    all_goals
      linarith
  have h4 : b = 1 ∨ b = 107 := by
    have h5 : b ∣ 107 := h3
    have h6 : b > 0 := by linarith
    have h7 : b ≤ 107 := by
      exact Int.le_of_dvd (by linarith) h5
    interval_cases b <;> try { 
      tauto 
    }
  rcases h4 with hb | hb
  · -- b = 1
    rw [hb] at eq6
    have eq7 : 3 * a ^ 2 = 108 := by
      nlinarith
    have eq8 : a ^ 2 = 36 := by
      nlinarith
    have eq9 : a = 6 := by
      have h10 : a ^ 2 = 36 := eq8
      have h11 : a > 0 := by linarith
      have h12 : a = 6 := by
        nlinarith
      exact h12
    rw [eq9, hb] at eq5
    nlinarith
  · -- b = 107
    rw [hb] at eq6
    exfalso
    omega