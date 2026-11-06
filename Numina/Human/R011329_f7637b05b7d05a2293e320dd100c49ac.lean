import Mathlib
/-[ Movement Problems ]

A green and a blue frog were 2015 meters apart from each other. At exactly 12:00 PM, the green frog jumped towards the blue frog by 9 meters. After a minute, the blue frog jumped towards the green frog by 8 meters. Another minute later, the green frog jumped again by 9 meters, and so on. At what time will the frogs meet? (Each jump occurs instantaneously.)-/
theorem algebra_235251 (s a t : ℚ) (hs : s = 2015 - 9)(ha : a = 8 + 9)(h : a * (t / 2) = s) : t = 236 := by
  rw [hs, ha] at h
  norm_num at h
  linarith