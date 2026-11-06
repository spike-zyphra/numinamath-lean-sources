import Mathlib

theorem algebra_20082 (d w l : ℝ) (h₀ : d = Real.sqrt (w^2 + l^2)) (h₁ : w = 300) (h₂ : l = 400) :
    l + w - d = 200 := by
  have hw : w = 300 := h₁
  have hl : l = 400 := h₂
  have h3 : d = 500 := by 
    rw [h₀, hw, hl]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    all_goals norm_num
  rw [h3, hw, hl]
  norm_num