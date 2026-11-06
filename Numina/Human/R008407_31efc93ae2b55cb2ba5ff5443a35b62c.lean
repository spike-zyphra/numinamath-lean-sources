import Mathlib

/- The smallest integer solution of the inequality $6-3x \lt 0$ is ______.-/
theorem algebra_9321 :IsLeast {x : ℤ | 6 - 3 * x < 0} 3 := by
  constructor
  -- If x = 3 then 6-3x < 0.
  . norm_num
  rintro x hx
  -- If x satisfies 6-3x < 0
  dsimp at hx
  -- It's obvious that 2 < x which is equivalent to 3 ≤ x.
  change 2 < x
  linarith
