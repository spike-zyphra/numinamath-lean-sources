import Mathlib

theorem algebra_107127 : (Nat.choose 2009 (2009 - 6 * 287)) * (-1 : ℤ)^287 = -Nat.choose 2009 287 := by
  have h1 : (2009 : ℕ) - 6 * 287 = 287 := by
    norm_num
  have h2 : (Nat.choose 2009 (2009 - 6 * 287) : ℤ) = (Nat.choose 2009 287 : ℤ) := by
    rw [show 2009 - 6 * 287 = 287 by
      norm_num
    ]
  rw [h2]
  have h3 : (-1 : ℤ) ^ 287 = -1 := by
    norm_num
  rw [h3]
  all_goals ring