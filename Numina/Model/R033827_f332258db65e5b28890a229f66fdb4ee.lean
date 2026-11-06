import Mathlib

theorem algebra_264710 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 1) :
    2 = a * (b ^ 2 + 1) / (a + b) + b * (c ^ 2 + 1) / (b + c) +
        c * (a ^ 2 + 1) / (c + a) := by
  have h1 : a + b ≠ 0 := by linarith
  have h2 : b + c ≠ 0 := by linarith
  have h3 : c + a ≠ 0 := by linarith

  have eq1 : a * (b ^ 2 + 1) / (a + b) = a * (b + c) := by
    have h_eq1 : b ^ 2 + 1 = (b + c) * (b + a) := by
      have h_eq2 : a * b + b * c + c * a = 1 := h
      nlinarith
    rw [h_eq1]
    field_simp [h1]
    all_goals ring

  have eq2 : b * (c ^ 2 + 1) / (b + c) = b * (c + a) := by
    have h_eq1 : c ^ 2 + 1 = (c + b) * (c + a) := by
      have h_eq2 : a * b + b * c + c * a = 1 := h
      nlinarith
    rw [h_eq1]
    field_simp [h2]
    all_goals ring

  have eq3 : c * (a ^ 2 + 1) / (c + a) = c * (a + b) := by
    have h_eq1 : a ^ 2 + 1 = (a + c) * (a + b) := by
      have h_eq2 : a * b + b * c + c * a = 1 := h
      nlinarith
    rw [h_eq1]
    field_simp [h3]
    all_goals ring

  rw [eq1, eq2, eq3]
  have eq4 : a * (b + c) + b * (c + a) + c * (a + b) = 2 := by
    nlinarith [h]
  linarith [eq4]