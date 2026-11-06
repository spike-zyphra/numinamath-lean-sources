import Mathlib

theorem algebra_173214 (d t : ℝ) (h₀ : d > 0) (h₁ : t > 0)
    (h₂ : d / t = 3500 / (t - d)) (h₃ : t / d = 4200 / (d - t)) :
    d * 4200 = 9100 := by
  have ht1 : t ≠ 0 := by linarith
  have ht2 : t - d ≠ 0 := by
    by_contra h
    have h4 : t = d := by linarith
    rw [h4] at h₂
    field_simp at h₂
    <;> nlinarith
  have hd0 : d ≠ 0 := by linarith
  have h4 : d - t ≠ 0 := by
    by_contra h
    have h5 : d = t := by linarith
    rw [h5] at h₃
    field_simp at h₃
    <;> nlinarith
  have eq1 : d * (t - d) = 3500 * t := by
    field_simp [ht1, ht2] at h₂
    nlinarith
  have eq2 : t * (d - t) = 4200 * d := by
    field_simp [hd0, h4] at h₃
    nlinarith
  nlinarith [sq_nonneg (d - t), sq_nonneg (d - 4200), sq_nonneg (t - 3500),
          mul_pos h₀ h₁
  ]