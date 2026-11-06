import Mathlib

theorem algebra_10873 {f : ℝ → ℝ} (hodd1 : ∀ x, f (x + 1) = - f (-x - 1)) (hodd2 : ∀ x, f (x - 1) = - f (-x - 1)) :
    ∀ x, f (x + 3) = - f (-x - 3) := by 
  intro x 
  calc
    f (x + 3) = f ((x + 2) + 1) := by ring_nf
    _ = - f (-(x + 2) - 1) := by rw [hodd1 (x + 2)]
    _ = - f (-x - 3) := by ring_nf