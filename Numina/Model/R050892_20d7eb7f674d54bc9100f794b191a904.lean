import Mathlib

theorem algebra_253384 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) (h' : ∃ x, x ∈ Set.Ioo 0 1 ∧ a * x ^ 2 + b * x + c = x) :
    2 * a + b > 1 := by
  rcases h' with ⟨x, ⟨hx1, hx2⟩, h_eq⟩
  have h_eq' : a * x^2 + b * x + c - x = 0 := by linarith
  have h_eq'' : a * x^2 + (b - 1) * x + c = 0 := by linarith
  have hc_eq : c = 1 - a - b := by linarith
  rw [hc_eq] at h_eq'
  -- Substitute c and simplify the equation
  have h_eq1 : a * x^2 + (b - 1) * x + (1 - a - b) = 0 := by linarith
  have h_eq3 : (x - 1) * (a * (x + 1) + b - 1) = 0 := by
    nlinarith [h_eq1]
  have h_eq4 : a * (x + 1) + b - 1 = 0 := by
    cases' (mul_eq_zero.mp h_eq3) with h_eq4 h_eq5
    · -- Contradiction with h_eq4 : x - 1 = 0
      exfalso
      nlinarith
    · -- Our desired result h_eq4 : a(x+1) + b - 1 = 0
      linarith
  have h_eq4' : a * (x + 1) + b = 1 := by linarith
  have h1 : x + 1 > 1 := by nlinarith
  nlinarith [h_eq4', h1]