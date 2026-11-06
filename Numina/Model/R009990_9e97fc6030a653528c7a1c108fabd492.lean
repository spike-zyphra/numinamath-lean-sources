import Mathlib

theorem algebra_14506 (x : ℂ) (h : x + (3 - 5 * .I) = 2 + 7 * .I) :
    x = -1 + 12 * .I := by 
  have hx : x = (2 + 7 * Complex.I) - (3 - 5 * Complex.I) := by 
    rw [← h]
    ring_nf
  rw [hx]
  ring_nf
  <;> norm_num [Complex.ext_iff]