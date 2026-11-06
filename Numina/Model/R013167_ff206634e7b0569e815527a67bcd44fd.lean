import Mathlib

theorem algebra_319746 {a b : ℝ} (h₀ : a * b ≠ 1) (h₁ : 5 * a^2 + 1995 * a + 8 = 0) (h₂ : 8 * b^2 + 1995 * b + 5 = 0) : a / b = 8 / 5 := by
  have hb : b ≠ 0 := by
    by_contra h
    rw [h] at h₂
    nlinarith
  have h3 : b ≠ 0 := hb
  have h4 : 5 * a^2 * b + 1995 * a * b + 8 * b = 0 := by
    have eq1 : 5 * a^2 + 1995 * a + 8 = 0 := h₁
    have eq2 : 5 * a^2 * b + 1995 * a * b + 8 * b = b * (5 * a^2 + 1995 * a + 8) := by ring
    rw [eq2]
    rw [eq1]
    norm_num
  have h5 : 8 * b^2 * a + 1995 * a * b + 5 * a = 0 := by
    have eq1 : 8 * b^2 + 1995 * b + 5 = 0 := h₂
    have eq2 : 8 * b^2 * a + 1995 * a * b + 5 * a = a * (8 * b^2 + 1995 * b + 5) := by ring
    rw [eq2]
    rw [eq1]
    norm_num
  have h6 : 5 * a^2 * b + 8 * b - (8 * b^2 * a + 5 * a) = 0 := by
    nlinarith [h4, h5]
  have h7 : 5 * a * (a * b - 1) + 8 * b * (1 - a * b) = 0 := by
    nlinarith [h6]
  have h8 : (a * b - 1) * (5 * a - 8 * b) = 0 := by
    nlinarith [h7]
  cases' (mul_eq_zero.mp h8) with h9 h10
  · -- Assume h9, a * b - 1 = 0, so a * b = 1
    have h11 : a * b = 1 := by linarith [h9]
    exfalso
    apply h₀
    linarith [h11]
  · -- Assume h10, 5 * a - 8 * b = 0
    have h12 : 5 * a = 8 * b := by linarith [h10]
    have h13 : a / b = 8 / 5 := by
      have h14 : b ≠ 0 := hb
      field_simp [h14]
      linarith [h12]
    exact h13