import Mathlib

theorem algebra_132971 (a b : ℝ) (h : ∃ x, x^2 + a * x + b^2 = 0 ∧ x^2 + b * x + a^2 = 0) :
    (a, b) = (0, 0) := by
  rcases h with ⟨x, hx1, hx2⟩
  have h1 : (a - b) * x + (b^2 - a^2) = 0 := by
    nlinarith
  have h2 : (a - b) * (x - (a + b)) = 0 := by
    nlinarith [h1]
  cases (mul_eq_zero.mp h2) with
  | inl h3 =>
    have hab : a = b := by linarith
    have eq1 := hx1
    rw [show b = a by linarith [hab]] at eq1
    have discriminant_eq : -3 * a^2 ≥ 0 := by
      nlinarith [sq_nonneg (x + a / 2)]
    have ha : a = 0 := by
      nlinarith
    have hb : b = 0 := by
      nlinarith [hab, ha]
    exact Prod.ext ha hb
  | inr h4 =>
    have hx_eq : x = a + b := by linarith
    rw [hx_eq] at hx1
    have eq1 : 2 * a^2 + 3 * a * b + 2 * b^2 = 0 := by
      nlinarith
    have eq2 : 2 * (a + 3 / 4 * b)^2 + (1 / 2) * b^2 = 0 := by
      nlinarith [eq1]
    have h_eq4 : 2 * (a + 3 / 4 * b)^2 ≥ 0 := by nlinarith
    have h_eq3 : (1 / 2) * b^2 ≥ 0 := by nlinarith
    have hb1 : b^2 = 0 := by
      nlinarith [eq2]
    have hb2 : b = 0 := by
      rw [sq_eq_zero_iff] at hb1
      exact hb1
    have ha1 : a = 0 := by
      nlinarith [hb2, eq1]
    exact Prod.ext ha1 hb2