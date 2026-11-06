import Mathlib

theorem number_theory_23082 (total_green total_red count : ℕ)
    (h₀ : total_green = 476 + 104 + 281) (h₁ : total_red = 32 + 16 + 80)
    (h₂ : count = min (total_green / 94) (total_red / 16)) :
    total_green - count * 94 = 109 := by
  norm_num [h₀, h₁, h₂] at *
  <;> omega