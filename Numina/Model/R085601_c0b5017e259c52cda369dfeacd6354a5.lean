import Mathlib

theorem algebra_6934 {a b c : ℝ} (h₀ : a^2 - a * b = 1) (h₁ : b^2 - b * c = 1)
    (h₂ : c^2 - a * c = 1) : a * b * c * (a + b + c) = -1 := by
  have ha : a ≠ 0 := by
    by_contra h
    rw [h] at h₀
    nlinarith
  have hb : b ≠ 0 := by
    by_contra h
    rw [h] at h₁
    nlinarith
  have hc : c ≠ 0 := by
    by_contra h
    rw [h] at h₂
    nlinarith
  have eq1 : a - b = 1 / a := by
    field_simp [ha]
    linarith
  have eq2 : b - c = 1 / b := by
    field_simp [hb]
    linarith
  have eq3 : c - a = 1 / c := by
    field_simp [hc]
    linarith
  have eq4 : (a - b) + (b - c) + (c - a) = 0 := by ring
  have eq5 : 1 / a + 1 / b + 1 / c = 0 := by
    linarith [eq1, eq2, eq3, eq4]
  have eq6 : a * b + b * c + c * a = 0 := by
    field_simp [ha, hb, hc] at eq5
    linarith
  have h3 : a^2 = a * b + 1 := by linarith
  have h4 : b^2 = b * c + 1 := by linarith
  have h5 : c^2 = a * c + 1 := by linarith
  have h6 : (a * b * c)^2 = (a * b + 1) * (b * c + 1) * (a * c + 1) := by
    rw [show (a * b * c)^2 = (a^2) * (b^2) * (c^2) by ring]
    rw [h3, h4, h5]
  nlinarith [h6, eq6]