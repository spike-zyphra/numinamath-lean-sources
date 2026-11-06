import Mathlib

theorem algebra_165669 {a b c : ℝ} (h₁ : a + b + c = 3) (h₂ : a^2 + b^2 + c^2 = 4) :
    (a^2 + b^2) / (2 - c) + (b^2 + c^2) / (2 - a) + (c^2 + a^2) / (2 - b) = 9 := by

  have h3 : a + b + c = 3 := h₁
  have h4 : a^2 + b^2 + c^2 = 4 := h₂

  have ha : 2 - a ≠ 0 := by
    by_contra h
    have ha : a = 2 := by linarith
    rw [ha] at h₁ h₂
    have h : b + c = 1 := by linarith
    have h' : b ^ 2 + c ^ 2 = 0 := by nlinarith
    have hb : b = 0 := by nlinarith
    have hc : c = 0 := by nlinarith
    linarith
  have hb : 2 - b ≠ 0 := by
    by_contra h
    have hb : b = 2 := by linarith
    rw [hb] at h₁ h₂
    have h : a + c = 1 := by linarith
    have h' : a ^ 2 + c ^ 2 = 0 := by nlinarith
    have ha : a = 0 := by nlinarith
    have hc : c = 0 := by nlinarith
    linarith
  have hc : 2 - c ≠ 0 := by
    by_contra h
    have hc : c = 2 := by linarith
    rw [hc] at h₁ h₂
    have h : a + b = 1 := by linarith
    have h' : a ^ 2 + b ^ 2 = 0 := by nlinarith
    have ha : a = 0 := by nlinarith
    have hb : b = 0 := by nlinarith
    linarith

  have eq1 : (a^2 + b^2) / (2 - c) = 2 + c := by
    have h : a^2 + b^2 = 4 - c^2 := by linarith
    rw [h]
    have h : 4 - c^2 = (2 - c) * (2 + c) := by
      ring
    rw [h]
    field_simp [hc]

  have eq2 : (b^2 + c^2) / (2 - a) = 2 + a := by
    have h : b^2 + c^2 = 4 - a^2 := by linarith
    rw [h]
    have h : 4 - a^2 = (2 - a) * (2 + a) := by
      ring
    rw [h]
    field_simp [ha]

  have eq3 : (c^2 + a^2) / (2 - b) = 2 + b := by
    have h : c^2 + a^2 = 4 - b^2 := by linarith
    rw [h]
    have h : 4 - b^2 = (2 - b) * (2 + b) := by
      ring
    rw [h]
    field_simp [hb]

  rw [eq1, eq2, eq3]
  linarith [h₁]