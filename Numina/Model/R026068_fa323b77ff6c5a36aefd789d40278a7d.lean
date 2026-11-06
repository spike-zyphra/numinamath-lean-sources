import Mathlib

theorem algebra_190094 {p q : ℝ} (h : (2 * p) ^ 2 + p * (2 * p) + q = 0 ∧ (p + q) ^ 2 + p * (p + q) + q = 0)
    (h' : 2 * p ≠ p + q) :
    p = 2 / 3 ∧ q = -8 / 3 := by 
  rcases h with ⟨h1, h2⟩
  have eq1 : q = -6 * p^2 := by
    nlinarith
  have eq2 : 2 * p^2 + 3 * p * q + q^2 + q = 0 := by
    nlinarith
  rw [eq1] at eq2
  have eq3 : 36 * p^4 - 18 * p^3 - 4 * p^2 = 0 := by 
    nlinarith
  have eq4 : p^2 * (36 * p^2 - 18 * p - 4) = 0 := by
    nlinarith
  cases (mul_eq_zero.1 eq4) with
  | inl h4 =>
    have hp : p = 0 := by
      nlinarith
    have hq : q = 0 := by
      rw [hp] at eq1
      nlinarith
    exfalso
    have h_eq : 2 * p = p + q := by
      rw [show p = 0 by linarith, show q = 0 by linarith]
      all_goals norm_num
    have h_ne : 2 * p ≠ p + q := h'
    contradiction
  | inr h5 =>
    have h6 : 36 * p^2 - 18 * p - 4 = 0 := by
      linarith
    have eq7 : (p - 2 / 3) * (p + 1 / 6) = 0 := by
      nlinarith
    cases (mul_eq_zero.1 eq7) with
    | inl hp1 =>
      have hp3 : p = 2 / 3 := by linarith
      have hq4 : q = -8 / 3 := by
        rw [hp3] at eq1
        nlinarith
      constructor
      · exact hp3
      · exact hq4
    | inr hp2 =>
      have hp4 : p = -1 / 6 := by linarith
      have hq4 : q = -1 / 6 := by
        rw [hp4] at eq1
        nlinarith
      exfalso
      have h_eq : 2 * p = p + q := by
        rw [show p = -1 / 6 by linarith, show q = -1 / 6 by linarith]
        all_goals norm_num
      have h_ne : 2 * p ≠ p + q := h'
      contradiction