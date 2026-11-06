import Mathlib

theorem algebra_253475 (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 240) (hsum : x * y + z = 46) (hsum' : x + y * z = 64) :
    x + y + z = 20 := by
  have h1 : x ≤ 45 := by
    nlinarith [hsum]

  have h2 : y ≤ 45 := by
    nlinarith [hsum]

  have h3 : z ≤ 45 := by
    nlinarith [hsum]

  interval_cases x <;> interval_cases y <;> omega