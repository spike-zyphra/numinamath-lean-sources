import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_145442 (f : ℝ → ℝ → ℝ)
  (h₀ : ∀ x y, f x y = x^2 + 2 * y^2 - 2 * x * y - x - 2 * y) :
  IsLeast {z | ∃ x y, z = f x y} (f 2 (3 / 2)) := by
  constructor
  · -- Show that f 2 (3/2) is in the image
    use 2, 3 / 2
    all_goals
      norm_num
      <;> linarith
  · -- Show that for any z in the image, f 2 (3/2) ≤ z
    intro z hz
    rcases hz with ⟨x, y, hxy⟩
    have h1 : f 2 (3 / 2) = -5 / 2 := by
      rw [h₀]
      norm_num
    have h2 : f x y = (x - (2 * y + 1) / 2) ^ 2 + (y - 3 / 2) ^ 2 - 5 / 2 := by
      rw [h₀]
      ring_nf
    have h3 : f x y ≥ -5 / 2 := by
      rw [h2]
      have h4 : (x - (2 * y + 1) / 2) ^ 2 ≥ 0 := by
        apply sq_nonneg
      have h5 : (y - 3 / 2) ^ 2 ≥ 0 := by
        apply sq_nonneg
      linarith
    linarith [hxy, h1, h3]