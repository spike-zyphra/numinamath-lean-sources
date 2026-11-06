import Mathlib

theorem other_162431 (u v w x : ℝ)
    (h₀ : u = 50 / 100) (h₁ : v = 60 / 100) (h₂ : w = 70 / 100) (h₃ : x = 80 / 100)
    (h₄ : 0 < u ∧ u < 1) (h₅ : 0 < v ∧ v < 1) (h₆ : 0 < w ∧ w < 1) (h₇ : 0 < x ∧ x < 1) :
    50 / u + 50 / v + 50 / w + 50 / x ≤ 1950 := by 
        rw [h₀, h₁, h₂, h₃]
        norm_num