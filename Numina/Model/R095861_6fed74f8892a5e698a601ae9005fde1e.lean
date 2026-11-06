import Mathlib

theorem algebra_2328 (c1 c2 c3: ℝ) (h₀ : c1 > 0.5) (h₁ : c2 = c1 * 0.9) (h₂ : c3 = c2 * 1.1): c3 < c1 := by
  have hc2 : c2 = c1 * 0.9 := h₁
  have hc3 : c3 = c2 * 1.1 := h₂
  rw [hc2] at hc3
  have hc3' : c3 = c1 * 0.99 := by
    calc 
      c3 = (c1 * 0.9) * 1.1 := hc3
      _ = c1 * (0.9 * 1.1) := by ring 
      _ = c1 * 0.99 := by norm_num 
  rw [hc3']
  nlinarith