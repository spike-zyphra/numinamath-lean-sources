import Mathlib

theorem algebra_240682 {S : ℝ} (hS : S = 25) (h1 h2 : ℝ)
    (h1_def : h1 = 1.5) (h2_def : h2 = 0.5) :
    (S * h1) / (S * h2) = 3 := by
  rw [h1_def, h2_def, hS]
  norm_num
  <;> ring_nf <;> norm_num