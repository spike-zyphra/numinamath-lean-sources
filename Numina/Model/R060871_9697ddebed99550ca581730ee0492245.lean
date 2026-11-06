import Mathlib

theorem algebra_323099 {A B C : ℝ} (hA : A = B * 1.5) (hC : C = B * 1.25) :
    A = C * (1 + 20 / 100) := by
  rw [hA, hC]
  ring_nf