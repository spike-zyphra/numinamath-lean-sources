import Mathlib


/-
Working together, Jack and Jill can paint a house in 3 days; Jill and Joe can paint the same house in 4 days; or Joe and Jack can paint the house in 6 days. If Jill, Joe, and Jack all work together, how many days will it take them?
-/
theorem algebra_611339  (jill jack joe : ℝ) (h1: 3*(jill + jack) = 1) (h2: 4*(jill + joe) = 1) (h3: 6*(joe + jack) = 1) : 8/3 * (jill + jack + joe) = 1 := by
  -- The equations given represent the collective rates of work for different pairs.

  -- Some simplifaiction is possible using basic arithmetic.

  have h1': jill + jack = 1/3 := by linarith
  have h2': jill + joe = 1/4 := by linarith
  have h3': joe + jack = 1/6 := by linarith

  -- We aim to find the combined rate when all three work together. This can be done by add the three  equations and devide it by 2.

  calc
    _  = 4/3 * (2*(joe + jill + jack)) := by ring_nf
    _ = 4/3 * ((jill + jack) + (jill + joe) + (joe + jack)) := by ring_nf
    _ = 4/3 * (1/3 + 1/4 + 1/6) := by rw [h1', h2', h3']
    _ = 1 := by norm_num