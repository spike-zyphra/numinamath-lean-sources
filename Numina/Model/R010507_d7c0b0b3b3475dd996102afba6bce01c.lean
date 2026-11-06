import Mathlib
theorem algebra_1123 (x xcomplement xsupplement : ℚ) (hxcomplement : xcomplement = 90 - x) (hxsupplement : xsupplement = 180 - x) (h : xcomplement = xsupplement / 4) : x = 60 := by
  rw [hxcomplement, hxsupplement] at h
  linarith