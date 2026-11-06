import Mathlib

open Real Set

theorem algebra_308524 (f : ℝ → ℝ → ℝ)
    (h₀ : ∀ x y, f x y = (y - 1)^2 + (x + y - 3)^2 + (2 * x + y - 6)^2) :
    IsLeast {z | ∃ x y, z = f x y} (f (5 / 2) (5 / 6)) := by
  constructor
  · -- Prove that `f (5 / 2) (5 / 6)` is in the set.
    refine' ⟨5 / 2, 5 / 6, rfl⟩
  · -- Prove that `f (5 / 2) (5 / 6)` is indeed the minimum
    intro z hz
    rcases hz with ⟨x, y, hz⟩
    have h1 : f (5 / 2) (5 / 6) = (1 / 6 : ℝ) := by
      rw [h₀]
      norm_num
    have h2 : f x y = (y - 1)^2 + (x + y - 3)^2 + (2 * x + y - 6)^2 := by
      apply h₀
    have h3 : (y - 1 : ℝ) ^ 2 + (x + y - 3 : ℝ) ^ 2 + (2 * x + y - 6 : ℝ) ^ 2 ≥ (1 / 6 : ℝ) := by
      nlinarith [sq_nonneg (x - 5 / 2), sq_nonneg (y - 5 / 6), 
          sq_nonneg ((x - 5 / 2) * 2 + (y - 5 / 6)), 
          sq_nonneg ((x - 5 / 2) + (y - 5 / 6)), 
          sq_nonneg ((x - 5 / 2) - (y - 5 / 6)), 
          sq_nonneg ((x + y) - (5/2 +5/6)), 
          sq_nonneg ((2 * x + y) - (2 * (5/2) +5/6))
          ]
    have h4 : f x y ≥ (1 / 6 : ℝ) := by
      rw [h2]
      linarith [h3]
    have h5 : z ≥ (1 / 6 : ℝ) := by
      linarith [hz, h4]
    linarith [h1, h5]