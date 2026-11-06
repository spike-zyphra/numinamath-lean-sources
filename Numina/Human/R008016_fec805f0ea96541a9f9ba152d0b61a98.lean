import Mathlib

/- Kelly drove north for 9 miles and then east for 12 miles at an average rate of 42 miles per hour to arrive at the town of Prime. Brenda left from the same location, at the same time, and drove along a straight road to Prime at an average rate of 45 miles per hour. How many minutes earlier than Kelly did Brenda arrive? -/
theorem algebra_20347 (d1 d2 v1 v2 : ℝ) (h1 : d1 = 9 + 12) (h2 : d2 = √(9^2 + 12^2)) (t1 : ℝ)
    (h3 : v1 = 42) (t2 : ℝ) (h4 : v2 = 45) (h5 : t1 = d1 / v1) (h6 : t2 = d2 / v2)
    : (t1 - t2) * 60 = 10 := by
  -- Brenda drove for $15$ miles
  have h2' : d2 = 15 := by
    rw [h2]
    refine (Real.sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_
    exact Nat.ofNat_pos'
    ring
  rw [h5, h6, h1, h3, h2', h4]
  ring