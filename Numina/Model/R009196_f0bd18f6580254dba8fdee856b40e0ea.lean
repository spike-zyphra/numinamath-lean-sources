import Mathlib.Tactic

theorem alg_1204
  (a : ℝ)
  (diff_vol : a ^ 3 - (a - 1) * a * (a + 1) = 5) :
  a ^ 3 = 125 := by
  -- Simplify the left side of the equation
  -- a^3 - (a - 1) * a * (a + 1)
  -- First compute (a - 1) * (a + 1) = a^2 - 1 (difference of squares)
  -- Then multiply by a: a * (a^2 - 1) = a^3 - a
  -- So a^3 - (a^3 - a) = a
  have eq1 : a ^ 3 - (a - 1) * a * (a + 1) = a := by
    ring
  
  -- Substitute the simplified equation into the hypothesis
  rw [eq1] at diff_vol
  
  -- Now we have a = 5
  have ha : a = 5 := by linarith
  
  -- Substitute a = 5 into a^3 and compute
  rw [ha]
  norm_num