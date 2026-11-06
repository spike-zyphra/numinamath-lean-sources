import Mathlib

theorem algebra_280772 (x : ℝ) (hx : x > 0) (h : 150000 + x = 20000 * (1 + 3.6 / 100) ^ 6 + 20000 * (1 + 4.5 / 100) ^ 6 + 20000 * (1 + 3.12 / 100) ^ 6 + 20000 * (1 + 0.25 / 100) ^ 6) :
    x = 29479.67 := by 
  ring_nf at h ⊢
  linarith