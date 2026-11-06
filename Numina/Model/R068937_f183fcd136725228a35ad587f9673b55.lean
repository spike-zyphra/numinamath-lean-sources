import Mathlib

theorem number_theory_193321 (M N : ℕ) (hMN : M < 10 ∧ N < 10)
    (h : 8 * 100000 + 10 * M + 420852 = 9 * 100000 + 10 * N + 9889788) :
    M = 5 ∧ N = 6 := by 
  omega