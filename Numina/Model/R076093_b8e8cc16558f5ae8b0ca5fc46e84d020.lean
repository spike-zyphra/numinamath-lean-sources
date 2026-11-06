import Mathlib

theorem algebra_95842 (m : ℝ) (h : ∃ a b, ∀ x, (a*x+b)^2 = (6*x^2+16*x+3*m)/6) :
    m = 32/9 := by
  rcases h with ⟨a, b, h_eq⟩
  have eq1 := h_eq 0
  have eq2 := h_eq 1
  have eq3 := h_eq (-1)
  have eq4 : b^2 = m / 2 := by
    nlinarith 
  have eq5 : (a + b) ^ 2 = (22 + 3 * m) / 6 := by 
    nlinarith
  have eq6 : (b - a) ^ 2 = (-10 + 3 * m) / 6 := by 
    nlinarith
  have eq10 : a^2 = 1 := by
    have eq7 : (a + b)^2 + (b - a)^2 = (22 + 3 * m) / 6 + (-10 + 3 * m) / 6 := by
      rw [eq5, eq6]
    have eq8 : (a + b)^2 + (b - a)^2 = 2 + m := by 
      nlinarith [eq7]
    have eq9 : a^2 + b^2 = (2 + m) / 2 := by 
      nlinarith 
    nlinarith [eq4, eq9]
  have ha1 : a = 1 ∨ a = -1 := by
    have h1 : a^2 = 1 := eq10
    have : a = 1 ∨ a = -1 := by 
      rw [sq_eq_one_iff] at h1
      exact h1
    assumption
  rcases ha1 with (rfl | rfl)
  · -- case a = 1
    have eq11 : (1 + b)^2 = (22 + 3 * m) / 6 := by 
      nlinarith 
    nlinarith [eq4, eq11]
  · -- case a = -1
    have eq11 : (-1 + b)^2 = (22 + 3 * m) / 6 := by 
      nlinarith 
    nlinarith [eq4, eq11]