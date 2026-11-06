import Mathlib

/- What is the least common multiple of 51, 68 and 85? -/
theorem algebra_21741 : lcm (lcm 51 68) 85 = 1020 := by
  -- lcm (lcm 51 68) 85 = lcm 204 85 = 1020
  calc lcm (lcm 51 68) 85
       _ = lcm 204 85 := by congrm lcm ?_ 85; simp [lcm, Nat.lcm]
       _ = 1020 := by simp [lcm, Nat.lcm]
