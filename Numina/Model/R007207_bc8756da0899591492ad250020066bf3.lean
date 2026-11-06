import Mathlib

open Classical

theorem amc_algebra_1193 (x : ℚ) (h : (10 - x) * (60 / 4) <= 30) : (x >= 8) := by
  norm_num at h
  linarith