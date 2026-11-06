import Mathlib

/--
If (1/9) times the base-`b` interpretation of "60" equals 5,
then (1/20) times the base-`b` interpretation of "80" equals 6.
-/
theorem algebra_610938 :
  ∃ b : ℕ, 10 ≤ b ∧
    (1 : ℚ) / 9 * (6 * b + 0) = 10 ∧
    (1 : ℚ) / 20 * (8 * b + 0) = 6 := by
  -- Solve the equation: (1/9) * (6 * b) = 5 → 6b = 45 → b = 15
  use 15
  constructor
  · norm_num  -- 15 ≥ 10
  constructor
  · norm_num  
  · norm_num  
