import Mathlib

/- Compute 2009^2 - 2008^2.-/
theorem algebra_608424 : 2009 ^ 2 - 2008 ^ 2 = 4017 := by
  calc
    _ = (2009 + 2008) * (2009 - 2008) := by ring_nf
    -- Apply difference of squares formula: a^2 - b^2 = (a+b)(a-b)
    _ = 4017 * 1 := by norm_num