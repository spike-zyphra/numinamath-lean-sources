import Mathlib

theorem algebra_235500 (unsorted_potatoes sorted_potatoes : ℝ)
    (h₀ : unsorted_potatoes > 0) (h₁ : sorted_potatoes > 0)
    (h₂ : (14 * unsorted_potatoes + 4 * sorted_potatoes) / (14 + 4) = unsorted_potatoes + 20) :
    sorted_potatoes - unsorted_potatoes = 90 := by

  norm_num at h₂
  linarith