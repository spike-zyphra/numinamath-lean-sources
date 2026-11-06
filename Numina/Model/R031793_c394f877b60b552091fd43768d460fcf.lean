import Mathlib

theorem algebra_96192 (a r : ℝ) (h₀ : a = Real.sqrt 3) (h₁ : r ≠ 0)
(h₂ : a * r = 3 ^ ((1 : ℝ) / 3)) (h₃ : a * r * r = 3 ^ ((1 : ℝ) / 6)) :
a * r * r * r = 1 := by
  have h₄ : r = (3 : ℝ) ^ (-(1 : ℝ) / 6) := by
    have h₅ : a * r = (3 : ℝ) ^ (1 / 3 : ℝ) := h₂
    have h₆ : a * r * r = (3 : ℝ) ^ (1 / 6 : ℝ) := h₃
    have h₇ : a * r * r = (a * r) * r := by ring
    rw [h₇] at h₆
    rw [h₅] at h₆
    have h₈ : r = ((3 : ℝ) ^ (1 / 6 : ℝ) ) / ( (3 : ℝ ) ^ (1 / 3 : ℝ) ) := by
      field_simp [h₁]
      all_goals linarith
    rw [h₈]
    have h₉ : ((3 : ℝ) ^ (1 / 6 : ℝ) ) / ( (3 : ℝ ) ^ (1 / 3 : ℝ) ) = (3 : ℝ) ^ (-(1 : ℝ) / 6) := by
      rw [← Real.rpow_sub]
      norm_num
      all_goals norm_num
    rw [h₉]
  calc
    a * r * r * r = (a * r * r) * r := by ring
    _ = (3 ^ ((1 : ℝ) / 6)) * r := by rw [h₃]
    _ = (3 ^ ((1 : ℝ) / 6)) * ( (3 : ℝ ) ^ (-(1 : ℝ) / 6) ) := by rw [h₄]
    _ = 1 := by
      rw [← Real.rpow_add]
      norm_num
      all_goals norm_num