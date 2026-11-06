import Mathlib

theorem algebra_1610 (d r t : ℝ) (hr : r = d / 40) (ht : t = d / 10) (hd : d > 0) :
    2 * d / (r + t) = 16 := by 
  rw [hr, ht]
  field_simp
  ring_nf