import Mathlib

theorem algebra_93903 (k : ℤ) (h : 2^1998 - 2^1997 - 2^1996 + 2^1995 = k * 2^1995) :
    k = 3 := by 
  have eq3 : (2^1998 - 2^1997 - 2^1996 + 2^1995 : ℤ) = (3 : ℤ) * 2^1995 := by 
    ring_nf
  rw [eq3] at h
  have h2 : (3 : ℤ) = k := by
    linarith
  linarith