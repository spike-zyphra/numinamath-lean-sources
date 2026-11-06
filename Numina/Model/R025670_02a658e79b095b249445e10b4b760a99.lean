import Mathlib

theorem algebra_176008 (d v : ℝ) (h₀ : d > 0) (h₁ : v > 0)
    (h₂ : d / 2 / (v + 30) + d / 2 / (v * (1 - 30 / 100)) = d / v) :
    v = 40 := by

  have h₃ : v + 30 ≠ 0 := by
    linarith

  have h₄ : v * (1 - 30 / 100 : ℝ) ≠ 0 := by
    have h₅ : (1 - 30 / 100 : ℝ) = (7 / 10 : ℝ) := by norm_num
    rw [h₅]
    have h₆ : v > 0 := h₁
    positivity

  have h₇ : d / 2 / (v + 30) + d / 2 / (v * (1 - 30 / 100)) = d / v := h₂

  have h₁₂ : (d / 2) / (v + 30) + (d / 2) / (v * (1 - 30 / 100)) - d / v = 0 := by linarith

  have h₁₃ : d * ((1 / 2) / (v + 30) + (1 / 2) / (v * (1 - 30 / 100)) - 1 / v) = 0 := by
    have h₆ : (d / 2) / (v + 30) + (d / 2) / (v * (1 - 30 / 100)) - d / v = 0 := h₁₂
    have h₁₄ : (d / 2) / (v + 30) + (d / 2) / (v * (1 - 30 / 100)) - d / v = d * ((1 / 2) / (v + 30) + (1 / 2) / (v * (1 - 30 / 100)) - 1 / v) := by
      field_simp [h₃, h₄, h₁]
      <;> ring
    rw [h₁₄] at h₆
    linarith

  cases (mul_eq_zero.mp h₁₃) with
  | inl h₁₄ =>
    linarith
  | inr h₁₅ =>
    have h₁₆ : (1 / 2 : ℝ) / (v + 30) + (1 / 2 : ℝ) / (v * (1 - 30 / 100)) - 1 / v = 0 := by
      linarith

    have h₁₇ : (1 - 30 / 100 : ℝ) = (7 / 10 : ℝ) := by norm_num
    rw [h₁₇] at h₁₆

    field_simp [(show v + 30 ≠ 0 by linarith), (show v ≠ 0 by linarith), (show (7 / 10 : ℝ) * v ≠ 0 by
      have h₁₈ : v > 0 := h₁
      nlinarith
    )] at h₁₆
    <;> nlinarith