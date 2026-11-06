import Mathlib

theorem algebra_198312 (s1 s2 t : ℝ) (h₀ : s1 = 60) (h₁ : s2 = 80) (h₂ : t = 1) :
    -(s2 * t + s1 * t) + 200 = 60 ∨ s1 * t - s2 * t + 200 = 180 ∨
    s2 * t - s1 * t + 200 = 220 ∨ s2 * t + s1 * t + 200 = 340 := by 
  rw [h₀, h₁, h₂]
  norm_num