import Mathlib

theorem algebra_11204 (C F : ℝ) (hC : C = 5 / 9 * (F - 32)) (hC1 : C = 20) : F = 68 := by
  rw [hC1] at hC
  have eq1 : 180 = 5 * (F - 32) := by 
    linarith
  linarith