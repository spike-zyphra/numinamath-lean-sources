import Mathlib

theorem algebra_15132 (total_burger : ℝ) (filler : ℝ) (h₀ : total_burger = 120) (h₁ : filler = 30) :
    (total_burger - filler) / total_burger * 100 = 75 := by
  rw [h₀, h₁]
  norm_num