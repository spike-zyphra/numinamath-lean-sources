import Mathlib

theorem algebra_53744 (c z n p : ℝ)
    (h₀ : c = 20 / 100)
    (h₁ : z = 1.5 * c)
    (h₂ : n = 1.5 * z)
    (h₃ : p = 1 - (c + z + n)) :
    p = 5 / 100 := by

  have hc : c = 20 / 100 := h₀

  have hz : z = 1.5 * (20 / 100 : ℝ) := by
    rw [h₁, hc]

  have hz_val : z = (30 / 100 : ℝ) := by
    rw [hz]
    norm_num

  have hn : n = 1.5 * (30 / 100 : ℝ) := by 
    rw [h₂, hz_val]

  have hn_val : n = (45 / 100 : ℝ) := by 
    rw [hn]
    norm_num

  calc 
    p = 1 - (c + z + n) := by 
      rw [h₃]
    _ = 1 - ((20 / 100 : ℝ) + (30 / 100 : ℝ) + (45 / 100 : ℝ)) := by 
      rw [hc, hz_val, hn_val]
    _ = 1 - (95 / 100 : ℝ) := by 
      norm_num
    _ = (5 / 100 : ℝ) := by 
      norm_num