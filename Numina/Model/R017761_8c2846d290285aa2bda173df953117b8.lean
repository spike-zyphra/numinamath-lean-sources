import Mathlib

open Real

lemma lemma_1 (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hb₃ : 0 < b₃) :
    a₁ ^ 2 / b₁ + a₂ ^ 2 / b₂ + a₃ ^ 2 / b₃ ≥ (a₁ + a₂ + a₃) ^ 2 / (b₁ + b₂ + b₃) := by
  have h1 : a₁ ^ 2 / b₁ + a₂ ^ 2 / b₂ + a₃ ^ 2 / b₃ - (a₁ + a₂ + a₃) ^ 2 / (b₁ + b₂ + b₃) ≥ 0 := by
    have h2 : 0 < b₁ * b₂ * b₃ * (b₁ + b₂ + b₃) := by
      positivity
    have h3 : (a₁ ^ 2 / b₁ + a₂ ^ 2 / b₂ + a₃ ^ 2 / b₃ - (a₁ + a₂ + a₃) ^ 2 / (b₁ + b₂ + b₃)) =
        ((a₁ ^ 2 * b₂ * b₃ * (b₁ + b₂ + b₃) + a₂ ^ 2 * b₁ * b₃ * (b₁ + b₂ + b₃) + a₃ ^ 2 * b₁ * b₂ * (b₁ + b₂ + b₃) - (a₁ + a₂ + a₃) ^ 2 * b₁ * b₂ * b₃)) / (b₁ * b₂ * b₃ * (b₁ + b₂ + b₃)) := by
      field_simp
      ring
    rw [h3]
    apply div_nonneg
    nlinarith [sq_nonneg (a₁ * b₂ - a₂ * b₁), sq_nonneg (a₁ * b₃ - a₃ * b₁), sq_nonneg (a₂ * b₃ - a₃ * b₂),
      sq_nonneg (a₁ * b₂ * b₃ - a₂ * b₁ * b₃), sq_nonneg (a₁ * b₂ * b₃ - a₃ * b₁ * b₂), sq_nonneg (a₂ * b₁ * b₃ - a₃ * b₁ * b₂),
      sq_nonneg (a₁ * (b₂ + b₃) - a₂ * b₃ - a₃ * b₂), sq_nonneg (a₂ * (b₁ + b₃) - a₁ * b₃ - a₃ * b₁), sq_nonneg (a₃ * (b₁ + b₂) - a₁ * b₂ - a₂ * b₁),
      mul_pos hb₁ hb₂, mul_pos hb₁ hb₃, mul_pos hb₂ hb₃,
      mul_pos (show 0 < b₁ * b₂ by positivity) (show 0 < b₃ by positivity)]
    positivity
  linarith

theorem inequalities_114467 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    1 / (x + y) + 4 / (y + z) + 9 / (x + z) ≥ 18 / (x + y + z) := by
  have hxy : 0 < x + y := by linarith
  have hyz : 0 < y + z := by linarith
  have hxz : 0 < x + z := by linarith
  have hx1 : 0 < x + y + z := by linarith
  have h12 : (1 : ℝ) ^ 2 / (x + y) + (2 : ℝ) ^ 2 / (y + z) + (3 : ℝ) ^ 2 / (x + z) ≥ (1 + 2 + 3 : ℝ) ^ 2 / ((x + y) + (y + z) + (x + z)) := by
    apply lemma_1 1 2 3 (x + y) (y + z) (x + z) (by linarith) (by linarith) (by linarith)
  have h3 : (1 : ℝ) ^ 2 / (x + y) + (2 : ℝ) ^ 2 / (y + z) + (3 : ℝ) ^ 2 / (x + z) = 1 / (x + y) + 4 / (y + z) + 9 / (x + z) := by
    norm_num
  rw [h3] at h12
  have h4 : (1 + 2 + 3 : ℝ) ^ 2 / ((x + y) + (y + z) + (x + z)) = 18 / (x + y + z) := by
    have h5 : (x + y) + (y + z) + (x + z) = 2 * (x + y + z) := by ring
    rw [h5]
    field_simp
    ring
  linarith [h12, h4]