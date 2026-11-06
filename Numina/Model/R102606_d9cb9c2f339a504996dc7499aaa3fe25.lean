import Mathlib

open Real Set

theorem algebra_598609 (f : ℝ → ℝ → ℝ)
    (h₀ : ∀ x y, f x y = (y - 1)^2 + (x + y - 3)^2 + (2 * x + y - 6)^2) :
    IsLeast {z | ∃ x y, z = f x y} (f (5 / 2) (5 / 6)) := by
  constructor
  · -- Show that f (5 / 2, 5 / 6) is in our set.
    use 5 / 2, 5 / 6
    all_goals norm_num [h₀]
  · -- For any z in the set, show that z ≥ f (5 / 2, 5 / 6).
    intro z h
    rcases h with ⟨x, y, h_eq⟩
    -- Express z = f(x, y) using the definition.
    have h1 : f x y = (y - 1)^2 + (x + y - 3)^2 + (2 * x + y - 6)^2 := h₀ x y
    have h2 : f (5 / 2) (5 / 6) = (5 / 6 - 1)^2 + (5 / 2 + 5 / 6 - 3)^2 + (2 * (5 / 2) + 5 / 6 - 6)^2 := by
      simp [h₀]
      all_goals norm_num
    have h3 : f x y ≥ f (5 / 2) (5 / 6) := by
      have h4 : (y - 1)^2 + (x + y - 3)^2 + (2 * x + y - 6)^2 ≥ (1 / 6 : ℝ) := by
        nlinarith [sq_nonneg (x - 5 / 2), sq_nonneg (y - 5 / 6), sq_nonneg (x - 5 / 2 + 2 * (y - 5 / 6)), sq_nonneg (x - 5 / 2 - (y - 5 / 6)), sq_nonneg (x - 5 / 2 - 44 / 25 * (y - 5 / 6)), sq_nonneg (x -5/2), sq_nonneg (y -5/6)]
      have h5 : f (5 / 2) (5 / 6) = (1 / 6 : ℝ) := by
        simp [h₀]
        all_goals norm_num
      linarith [show (y - 1)^2 + (x + y - 3)^2 + (2 * x + y - 6)^2 = f x y by linarith [h1], h4, h5]
    linarith [h_eq, show f x y ≥ f (5 / 2) (5 / 6) by linarith [h3]]