import Mathlib

theorem number_theory_109327 {N : ℕ} (hN : N > 70) (h : 21 * N % 70 = 0) :
    N ≥ 80 := by 
  omega