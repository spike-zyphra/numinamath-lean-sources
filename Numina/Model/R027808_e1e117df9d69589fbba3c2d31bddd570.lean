import Mathlib

theorem algebra_15220 {a b : ℤ} (ha : 0 < a) (hb : 0 < b)
    (h : (a + Complex.I * b) ^ 2 = 3 + 4 * Complex.I) :
    a + Complex.I * b = 2 + Complex.I := by
  have eq1 := congr_arg Complex.re h
  have eq2 := congr_arg Complex.im h
  simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eq1 eq2
  have h_eq1 : (a : ℝ) ^ 2 - (b : ℝ) ^ 2 = 3 := by
    ring_nf at eq1 ⊢
    nlinarith
  have h_eq2 : 2 * (a : ℝ) * (b : ℝ) = 4 := by
    ring_nf at eq2 ⊢
    nlinarith
  have eq3 : a ^ 2 - b ^ 2 = 3 := by
    have h1 : (a ^ 2 - b ^ 2 : ℝ) = (3 : ℝ) := by linarith
    exact_mod_cast h1
  have eq4 : 2 * (a : ℤ) * (b : ℤ) = 4 := by
    have h2 : (2 * (a : ℝ) * (b : ℝ) : ℝ) = (4 : ℝ) := by linarith
    exact_mod_cast h2
  have h_eq3 : (a : ℤ) * (b : ℤ) = 2 := by
    nlinarith
  have h_eq4 : a * b = 2 := by exact_mod_cast h_eq3
  have h10 : a ∣ 2 := by
    use b
    all_goals
      nlinarith
  have h11 : a = 1 ∨ a = 2 := by
    have h2 : a ∣ 2 := h10
    have h3 : a > 0 := by linarith
    have h4 : a ≤ 2 := by
      exact Int.le_of_dvd (by linarith) h2
    interval_cases a <;> try { tauto }
  rcases h11 with (ha1 | ha2)
  · -- Case a = 1
    have ha1' : a = 1 := by linarith
    have hb2' : b = 2 := by
      rw [show a = 1 by linarith] at h_eq4
      nlinarith
    rw [show a = 1 by linarith, show b = 2 by linarith] at eq3
    nlinarith
  · -- Case a = 2
    have ha2' : a = 2 := by linarith
    have hb1' : b = 1 := by
      rw [show a = 2 by linarith] at h_eq4
      nlinarith
    have h9 : a = 2 := by linarith
    have h10 : b = 1 := by linarith
    simp [h9, h10]