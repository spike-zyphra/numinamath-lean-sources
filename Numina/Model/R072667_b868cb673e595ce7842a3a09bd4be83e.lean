import Mathlib

theorem algebra_108940 (d p v : ℝ) (h₀ : d > 0) (h₁ : p > 0) (h₂ : v > 0)
    (h₃ : p = (1 - 25 / 100) * v) (h₄ : p * (1 + 25 / 100) = d) :
    d / v < d / p := by
  have h7 : p < v := by
    nlinarith [h₃, h₂]
  have pos1 : v * p > 0 := by
    apply mul_pos
    all_goals linarith
  have pos2 : d * (p - v) < 0 := by
    have : p - v < 0 := by linarith
    have hd : d > 0 := h₀
    nlinarith
  have h8 : d / v - d / p < 0 := by
    have h9 : d / v - d / p = (d * (p - v)) / (v * p) := by
      field_simp
      <;> ring
    rw [h9]
    apply div_neg_of_neg_of_pos
    linarith
    positivity
  linarith