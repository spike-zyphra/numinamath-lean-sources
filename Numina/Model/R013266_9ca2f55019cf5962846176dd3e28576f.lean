import Mathlib

theorem algebra_4179 (a : ℝ) (h₀ : a = √2 - 1) :
    1 / a^3 - 2 / a^2 - 1 / a = 0 := by
  have h₁ : a = √2 - 1 := h₀
  have h2 : a ≠ 0 := by
    rw [h₁]
    have h3 : √2 > 1 := by
      have h4 : 1 < (2 : ℝ) := by norm_num
      have h5 : √1 < √2 := Real.sqrt_lt_sqrt (by norm_num) (by linarith)
      have h6 : √1 = 1 := Real.sqrt_one
      linarith [h5, h6]
    have h7 : √2 - 1 > 0 := by linarith [h3]
    linarith
  have h3 : a + 1 = √2 := by
    rw [h₁]
    all_goals ring
  have h3' : (a + 1)^2 = 2 := by
    rw [h3]
    all_goals norm_num
  have h4 : a^2 + 2 * a - 1 = 0 := by
    nlinarith [h3']
  have h5 : a^2 = 1 - 2 * a := by
    nlinarith
  have h6 : 1 / a^3 - 2 / a^2 - 1 / a = (1 - 2 * a - a^2) / a^3 := by
    field_simp [h2]
    <;> ring
  rw [h6]
  have h7 : 1 - 2 * a - a^2 = 0 := by
    nlinarith [h4, h5]
  rw [h7]
  all_goals norm_num