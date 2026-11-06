import Mathlib

theorem number_theory_2482
    (N : ℤ)
    (hN : N = 1992 * 1993 * 1994 + 1993 * 1994 * 1995 + 1994 * 1995 * 1996 + 1995 * 1996 * 1997) :
    N % 10 = 4 := by
  rw [hN]
  norm_num