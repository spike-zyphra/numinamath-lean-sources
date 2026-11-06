import Mathlib

theorem algebra_265369 (d : ℝ) (h : d > 0) (h1 : 8.4 / 100 * d = 6.3 / 100 * d + 400 / 0.80) :
    d ∈ Set.Ioo 22000 26000 := by
  have h2 : d > 22000 := by
    norm_num at h1
    linarith
  have h3 : d < 26000 := by
    norm_num at h1
    linarith
  constructor
  · linarith
  · linarith