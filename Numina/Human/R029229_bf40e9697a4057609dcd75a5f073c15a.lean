import Mathlib

/- The AIME Triathlon consists of a half-mile swim, a 30-mile bicycle ride, and an eight-mile run. Tom swims, bicycles, and runs at constant rates. He runs fives times as fast as he swims, and he bicycles twice as fast as he runs. Tom completes the AIME Triathlon in four and a quarter hours. How many minutes does he spend bicycling? -/

theorem algebra_95404 (s b r : ℝ) (_ : s > 0) (_ : b > 0) (_ : r > 0) (hr : r = 5 * s) (hb : b = 2 * r)
    (h : 0.5/s + 30/b + 8/r = 4.25 * 60) : 30/b = 150 := by
  -- r is the running speed, b is the biking speed, and s is the swimming speed
  -- We rewrite everything in terms of s
  rw [hr, hb] at *
  ring_nf at h
  -- We solve the equation
  have : s = (51/10)/255 := by rw [← h]; ring_nf; exact Eq.symm (DivisionMonoid.inv_inv s)
  -- We susbtitute back to get the answer
  rw [this]
  norm_num