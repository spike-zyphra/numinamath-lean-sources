import Mathlib

theorem algebra_288773 (l is : ℝ) (hl : l > 0) (his : is > 0)
    (h : is = l * 1.25) (h1 : is * 3 = l * 5) :
    l * 17 = is * 3 := by
  rw [h] at h1
  ring_nf at h1
  nlinarith