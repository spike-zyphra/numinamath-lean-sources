import Mathlib

theorem algebra_240780 (h1 h2 : ℝ) (h1' : h1 = 1.5) (h2' : h2 = 0.5)
    (S : ℝ) (hS : S = 25) (ρ : ℝ) (hρ : ρ = 1) :
    (ρ * S * h1) / (S * h2) = 3 := by
  rw [hρ, hS, h1', h2']
  norm_num