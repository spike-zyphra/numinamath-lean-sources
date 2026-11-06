import Mathlib

/-Let N denote the sum of the decimal digits of
(1000 10). Estimate the value of N. If your answer is a positive integer A written fully in
notation (for example, 521495223 ), your score will be the greatest integer not exceeding
25⋅(0.99)∣A−N∣. Otherwise, your score will be zero.-/

theorem combinatorics_609413: (Nat.digits 10 (Nat.choose 1000 100)).sum = 621 := by

  native_decide