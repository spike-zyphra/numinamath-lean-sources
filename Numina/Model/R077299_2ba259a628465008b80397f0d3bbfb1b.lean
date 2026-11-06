import Mathlib

theorem algebra_212710 {A B C : ℤ} (hA : A = 500) (hB : B = -1) (hC : C = -500) :
    (A / 999 : ℚ) + (B / 1000 : ℚ) + (C / 1001 : ℚ) = 1 / (999 * 1000 * 1001) := by 
  rw [hA, hB, hC]
  norm_num