import Mathlib

theorem algebra_20062 {V I R : ℝ} (hV : V = I * R) (hI : I = 40) (hR : R = 3) :
    ∃ x, x * 20 = V := by
  have hV' : V = 120 := by
    rw [hV, hI, hR]
    norm_num
  use 6
  rw [hV']
  norm_num