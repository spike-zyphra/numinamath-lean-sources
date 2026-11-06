import Mathlib

theorem algebra_167170 (d : ℝ) (h₀ : d = 475) (v : ℝ) (h₁ : v = 475 / (3 * 60 + 10)) (x : ℝ)
    (hx : x = 57 / v) (h₂ : x * 100 = 8 * 120) :
    d / v = 237.5 := by

  have h3 : v = 475 / (3 * 60 + 10 : ℝ) := h₁
  have hv : v ≠ 0 := by
    rw [h3]
    norm_num
  have h4 : (57 / v) * 100 = 8 * 120 := by 
    rw [show x = 57 / v by linarith [hx]] at h₂
    linarith [h₂]

  rw [show v = 475 / (3 * 60 + 10 : ℝ) by linarith [h₁]] at h4
  norm_num at h4
  all_goals
    norm_num [h₀, h₁] at *
    all_goals
      field_simp at h4 ⊢
      all_goals
        linarith