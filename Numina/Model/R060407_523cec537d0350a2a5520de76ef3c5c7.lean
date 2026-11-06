import Mathlib

theorem algebra_317922 {a : ℝ} (ha : 0 < a) (h1 : (1 - a / 100) * (1 + 12 / 100) = 1.56) :
    a = 2 := by
  norm_num at h1 ⊢
  linarith