import Mathlib

/- The arithmetic mean of nine numbers is 54. If two numbers $u$ and $v$ are added to the list, the mean of the eleven-member list becomes 66. What is the mean of $u$ and $v$? -/
theorem algebra_13843 (u v : ℝ) (h₁ : (9 * 54 + u + v) / 11 = 66) :
    (u + v) / 2 = 120 := by
  nlinarith