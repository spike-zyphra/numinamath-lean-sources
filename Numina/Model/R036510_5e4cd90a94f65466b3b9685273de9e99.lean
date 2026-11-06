import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_199142 (f : ℝ → ℝ → ℝ)
  (h₀ : ∀ x y, f x y = x^2 + 2 * x * y + 2 * y^2 + 2 * x + 4 * y + 3) :
  IsLeast {z | ∃ x y, z = f x y} (f 0 (-1)) ∧ f 0 (-1) = 1 := by

  constructor
  · -- We need to prove that f(0, -1) is the least element in {z | ∃ x y, z = f x y}
    constructor
    · -- Let's prove that f(0, -1) is in the image
      use 0, -1
      all_goals
        norm_num [h₀]
    · -- Let's prove the minimality
      intro z hz
      rcases hz with ⟨x, y, hz⟩

      have h1 : f x y = (x + y + 1) ^ 2 + (y + 1) ^ 2 + 1 := by
        rw [h₀]
        ring
      have h2 : f 0 (-1) = 1 := by
        rw [h₀]
        norm_num
      have h3 : f x y ≥ 1 := by
        rw [h1]
        nlinarith [sq_nonneg (x + y + 1), sq_nonneg (y + 1)]
      have h4 : f 0 (-1) ≤ f x y := by
        rw [h2]
        linarith [h3]

      linarith [hz, h4]

  · -- Let's prove that f(0, -1) = 1
    rw [h₀]
    norm_num