import Mathlib

theorem algebra_201751 (d : ℝ) (h : d = 12) :
    2 * d = 24 ∧ (21 - d) = 9 := by
  rw [h]
  constructor
  · -- show that 2 * 12 = 24
    norm_num
  · -- show that 21 - 12 = 9
    norm_num