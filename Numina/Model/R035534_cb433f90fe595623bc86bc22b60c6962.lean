import Mathlib

theorem algebra_100305 (a b c : ℝ) (h₀ : a + b + c = 4) (h₁ : a^2 + b^2 + c^2 = 12) (h₂ : a * b * c = 1) :
    ¬(a > 0 ∧ b > 0 ∧ c > 0) := by 
  intro h
  rcases h with ⟨ha, hb, hc⟩

  have h₃ : a * b + a * c + b * c = 2 := by 
    have : a * b + a * c + b * c = 2 := by 
      have h₃1 : a + b + c = 4 := h₀
      have h₃2 : a^2 + b^2 + c^2 = 12 := h₁
      have h₃3 : a * b + a * c + b * c = ( (a + b + c) ^ 2 - (a^2 + b^2 + c^2) ) / 2 := by
        ring_nf
      rw [h₃3]
      rw [h₃1, h₃2]
      norm_num
    linarith
  
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  all_goals linarith