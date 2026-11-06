import Mathlib

theorem number_theory_283994 (h : (8 * 60 + 9) % 7 = 0) :
    (8 * 60 + 2) % 7 = 0 := by 
  norm_num at h ⊢