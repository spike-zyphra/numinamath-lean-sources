import Mathlib
theorem algebra_235251 (s a t : ℚ) (hs : s = 2015 - 9)(ha : a = 8 + 9)(h : a * (t / 2) = s) : t = 236 := by
  rw [ha, hs] at h
  norm_num at h
  linarith