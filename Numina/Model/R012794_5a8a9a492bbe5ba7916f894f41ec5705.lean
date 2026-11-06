import Mathlib

theorem algebra_118639 (f : ℝ → ℝ → ℝ)
    (h₀ : ∀ x y, f x y = (y - 1)^2 + (x + y - 3)^2 + (2 * x + y - 6)^2) :
    IsLeast {z | ∃ x y, z = f x y} (f (5 / 2) (5 / 6)) := by
  constructor
  · -- Show that f (5 / 2) (5 / 6) is in the set.
    refine ⟨5 / 2, 5 / 6, rfl⟩
  · -- Show that f (5 / 2) (5 / 6) is the least element in the set
    intro z hz
    rcases hz with ⟨x, y, hz⟩
    have h1 : f x y = (y - 1)^2 + (x + y - 3)^2 + (2 * x + y - 6)^2 := by
      apply h₀
    have h2 : f (5 / 2) (5 / 6) = (1 / 6 : ℝ) := by
      rw [h₀]
      norm_num
    have h3 : (y - 1 : ℝ)^2 + (x + y - 3)^2 + (2 * x + y - 6)^2 ≥ (1 / 6 : ℝ) := by
      nlinarith [sq_nonneg (x - 5 / 2), sq_nonneg (y - 5 / 6),
          sq_nonneg ((x - 5 / 2) - (y - 5 / 6) * 2),
          sq_nonneg ((x - 5 / 2) + (y - 5 / 6) * 3 / 2)
        ]
    have h4 : f x y ≥ (1 / 6 : ℝ) := by
      rw [h1]
      linarith
    have h5 : f (5 / 2) (5 / 6) ≤ f x y := by
      linarith [h2, h4]
    linarith [hz, h5]