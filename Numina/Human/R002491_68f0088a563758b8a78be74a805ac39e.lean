import Mathlib

/--
Cindy was asked by her teacher to subtract 3 from a certain number and then divide the result by 9. Instead, she subtracted 9 and then divided the result by 3, giving an answer of 43. What would her answer have been had she worked the problem correctly?
-/
theorem algebra_1122 (n x : ℚ) (h1 : x = (n - 3) / 9) (h2 : 43 = (n - 9) / 3) : x = 15 := by linarith