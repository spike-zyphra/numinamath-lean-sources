import Mathlib

open Real

theorem calculus_22636 : ∃ n : ℕ, n ≤ 180 ∧ cos (n * π / 180) = cos (568 * π / 180) := by 
  use 152
  constructor
  · norm_num 
  · -- Show that cos(152°) = cos(568°)
    have h1 : cos (152 * π / 180) = cos (568 * π / 180) := by
      have h2 : 568 * π / 180 = 208 * π / 180 + 2 * π := by 
        ring_nf 
      have h3 : cos (208 * π / 180 + 2 * π) = cos (208 * π / 180) := by 
        rw [cos_add_two_pi] 
      have h4 : cos (208 * π / 180) = -cos (28 * π / 180) := by 
        have h5 : 208 * π / 180 = π + 28 * π / 180 := by 
          ring_nf 
        rw [h5]
        rw [cos_add]
        rw [cos_pi, sin_pi]
        ring 
      have h4' : cos (152 * π / 180) = -cos (28 * π / 180) := by 
        have h5 : 152 * π / 180 = π - 28 * π / 180 := by 
          ring_nf 
        rw [h5]
        rw [cos_sub]
        rw [cos_pi, sin_pi]
        ring 
      have h3' : cos (568 * π / 180) = cos (208 * π / 180) := by 
        rw [h2]
        rw [h3]
      linarith [h4, h4', h3']
    linarith [h1]