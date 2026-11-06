import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem inequalities_124916
    (x y : ℝ)
    (h₀ : 0 < x)
    (h₁ : 0 < y)
    (h₂ : x + y = 1) :
    9 ≤ (1 + 1 / x) * (1 + 1 / y) := by
  have h3 : 0 < x * y := by
    nlinarith [mul_pos h₀ h₁]
  have h4 : (1 + 1 / x) * (1 + 1 / y) = 1 + 2 / (x * y) := by
    field_simp
    <;> nlinarith [h₂]
  have h5 : x * y ≤ 1 / 4 := by
    nlinarith [sq_nonneg (x - y), h₂]
  have h6 : 2 / (x * y) ≥ 8 := by
    have h7 : 0 < x * y := h3
    have h8 : x * y ≤ 1 / 4 := h5
    have h9 : (2 : ℝ) / (x * y) ≥ (2 : ℝ) / (1 / 4) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [h8]
    have h10 : (2 : ℝ) / (1 / 4) = 8 := by
      norm_num
    linarith
  nlinarith [h4, h6]