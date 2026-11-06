import Mathlib

theorem algebra_307102 {x y : ℝ} (hx : (x - 1)^3 + 1997 * (x - 1) = -1) (hy : (y - 1)^3 + 1997 * (y - 1) = 1) :
    x + y = 2 := by
  have eqn : (x - 1) + (y - 1) = 0 := by
    have sum_eq_zero : (x - 1) ^ 3 + (y - 1) ^ 3 + 1997 * ( (x - 1) + (y - 1)) = 0 := by
      linarith [hx, hy]
 
    have factored : ((x - 1) + (y - 1)) * ( ( (x - 1) + (y - 1) ) ^ 2 - 3 * ((x - 1) * (y - 1)) + 1997 ) = 0 := by 
      nlinarith [sq_nonneg ((x - 1) - (y - 1)), sq_nonneg ((x - 1) + (y - 1)), sq_nonneg ((x - 1) * (y - 1) - 665) ]

    cases' (mul_eq_zero.mp factored) with h1 h2
    ·
      linarith 
    · -- Second case where the second factor is zero
      -- Let's add contradiction to the system.
      nlinarith [sq_nonneg ((x - 1) - (y - 1)), sq_nonneg ((x - 1) + (y - 1)), sq_nonneg ((x - 1) * (y - 1) - 665) ]

  -- Now, transforming (x-1) + (y-1) = 0 into x + y = 2
  linarith