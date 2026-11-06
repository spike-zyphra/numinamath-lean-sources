import Mathlib

theorem algebra_214301 {p q : ℤ} (hp : p ≠ 0) (hq : q ≠ 0)
    (h : ∃ x y, x^2 + p * x + q = 0 ∧ y^2 + p * y + q = 0 ∧ x = p ∧ y = q) :
    p = 1 ∧ q = -2 := by
  rcases h with ⟨x, y, hx, hy, hx2, hy2⟩
  rw [hx2] at hx
  rw [hy2] at hy
  have eq1 : 2 * p^2 + q = 0 := by
    nlinarith
  have eq2 : q^2 + p * q + q = 0 := by
    nlinarith
  have eq3 : q = -2 * p^2 := by
    nlinarith
  rw [eq3] at eq2
  have eq4 : 2 * p^2 * (2 * p^2 - p - 1) = 0 := by 
    nlinarith
  cases' (mul_eq_zero.1 eq4) with h1 h2
  · -- First case: 2 * p^2 = 0
    have hp2 : p^2 = 0 := by
      nlinarith
    have hp0 : p = 0 := by 
      nlinarith
    contradiction
  · -- Second case: 2 * p^2 - p - 1 = 0
    have eq5 : 2 * p^2 - p - 1 = 0 := by 
      nlinarith
    have eq6 : (2 * p + 1) * (p - 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 eq6) with h3 h4
    · -- First case: 2 * p + 1 = 0
      have h3' : p = 0 := by
        omega
      contradiction
    · -- Second case: p - 1 = 0 
      have hp1 : p = 1 := by
        nlinarith
      have hq1 : q = -2 := by
        rw [hp1] at eq3
        nlinarith
      exact ⟨hp1, hq1⟩