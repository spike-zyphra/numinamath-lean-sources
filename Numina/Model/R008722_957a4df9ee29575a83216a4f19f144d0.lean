import Mathlib

theorem algebra_12580 (k : ℤ) (kpos : k > 0) (h : (2 ^ 1004 + 5 ^ 1005)^2 - (2 ^ 1004 - 5 ^ 1005)^2 = k * 10 ^ 1004) : k = 20 := by
  ring_nf at h
  omega