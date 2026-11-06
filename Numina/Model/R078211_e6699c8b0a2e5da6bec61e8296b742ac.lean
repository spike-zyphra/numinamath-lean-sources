import Mathlib

theorem algebra_325731 {f : ℝ → ℝ} (hodd : ∀ x, f (x + 1) = -f (-x - 1)) (hodd' : ∀ x, f (x - 1) = -f (-x - 1)) :
    ∀ x, f (x + 3) = -f (-x - 3) := by
  intro x
  have h1 := hodd (x + 2)
  rw [show (x + 2) + 1 = x + 3 by ring] at h1
  rw [show -(x + 2) - 1 = -x - 3 by ring] at h1
  linarith