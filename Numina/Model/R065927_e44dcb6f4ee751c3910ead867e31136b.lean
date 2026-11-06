import Mathlib

theorem algebra_14926 {x : ℝ} (hx : x ≠ 0) (h : (30 / x) = 1.5) : x = 20 := by
  -- Find x s.t. 30/x = 1.5.
  -- This is equivalent to solving (30 / x) = (3 / 2).
  -- The goal is to prove x = 20.
  have h1 : x ≠ 0 := hx
  field_simp [h1] at h
  -- This repeats the calculation process of division elimination in algebra, convert $30/x = 1.5$ to $30 = 1.5 * x$.
  ring_nf at h 
  -- Simplify $1.5 * 20$.
  -- h can be divided into linear strict sense.
  -- Solve linear arithmetic to get x = 20.
  linarith