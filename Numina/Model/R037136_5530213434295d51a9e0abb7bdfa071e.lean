import Mathlib

theorem algebra_94250 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) 
(h : ∃ x y, x = a ∧ y = b ∧ x^2 + a * x + b = 0 ∧ y^2 + a * y + b = 0) :
a = 1 ∧ b = -2 := by
  rcases h with ⟨x, y, hx_eq_a, hy_eq_b, h1, h2⟩
  rw [hx_eq_a] at h1
  rw [hy_eq_b] at h2
  have eq1 : 2*a^2 + b = 0 := by
    nlinarith
  have eq2 : b^2 + a * b + b = 0 := by
    nlinarith [h2]
  have eq3 : b * (b + a + 1) = 0 := by
    nlinarith [eq2]
  cases' (mul_eq_zero.1 eq3) with hb1 h4
  · -- hb1: b = 0
    exfalso
    apply hb
    linarith
  · -- h4: b + a + 1 = 0
    have eq3' : b = -a - 1 := by linarith
    rw [eq3'] at eq1
    have eq4 : 2 * a^2 - a - 1 = 0 := by linarith [eq1]
    have h6 : (a - 1) * (2 * a + 1) = 0 := by
      nlinarith [eq4]
    cases' (mul_eq_zero.1 h6) with ha1 ha2
    · -- ha1: a - 1 = 0
      have ha1' : a = 1 := by linarith
      have hb' : b = -2 := by
        nlinarith [ha1', eq3']
      exact ⟨by linarith, by linarith⟩
    · -- ha2: 2 * a + 1 = 0
      have ha2' : a = -1 / 2 := by linarith
      have hb_eq : b = -1 / 2 := by
        nlinarith [ha2', eq3']
      exfalso
      have hneq : a = b := by 
        nlinarith [ha2', hb_eq]
      have hne : a ≠ b := by
        exact hab
      contradiction