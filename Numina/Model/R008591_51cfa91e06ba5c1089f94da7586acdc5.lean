import Mathlib

theorem algebra_93329 (h m takeoff landing : ℤ) (ht : takeoff = 60 * 10 + 34) (hl : landing = 60 * 12 + 60 * 1 + 18)
(hm : m = (landing - takeoff) % 60) (hh: 60 * h = landing - takeoff - m):
h + m = 46 := by
  rw [ht] at *
  rw [hl] at *
  omega