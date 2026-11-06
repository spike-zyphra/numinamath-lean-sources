import Mathlib

theorem algebra_275962 (d : ℝ) (h : d > 0) (h1 : 8.4 * d / 100 * 0.80 = 400 + 6.3 * d / 100 * 0.80) :
    d ∈ Set.Ioo 22000 26000 := by
  have h2 : d > 22000 := by
    norm_num at h1
    linarith
  have h3 : d < 26000 := by
    norm_num at h1
    linarith
  constructor <;> linarith