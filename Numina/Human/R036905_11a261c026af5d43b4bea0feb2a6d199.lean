import Mathlib

theorem number_theory_6047 (n : ℕ) (h : n > 0) (h1 : Odd n) (h2 : 596 = (n^2) + ((n+2)^2) + ((n+4)^2) + ((n+6)^2)) :
    n = 9 := by 
  ring_nf at h2
  nlinarith [h, h1, sq_nonneg (n - 9)]