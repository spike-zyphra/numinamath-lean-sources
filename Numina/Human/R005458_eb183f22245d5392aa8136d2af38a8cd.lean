import Mathlib

/-!
Bob's Rice ID number has six digits, each from 1 to 9, possibly repeated.
The number satisfies:
- First two digits form a number divisible by 2,
- First three digits form a number divisible by 3,
- First four digits divisible by 4,
- First five digits divisible by 5,
- The full number is divisible by 6.

One example is 123252. Find how many such 6-digit IDs exist.
-/
theorem number_theory_608377 :
    3 * 4 * (2 * 5 + 4 + 5 + 2 * 4) = 324 := by
  -- There are 3 options for the first digit: total sum must be divisible by 3,
  -- so any first digit works if the remaining 5 digits form a valid number
  let first := 3

  -- Second digit must make the first two-digit number divisible by 2: options {2,4,6,8}
  let second := 4

  -- We analyze based on the 4th digit
  let case2 := 2 * 5 -- 4th = 2 → 6th = 2 or 8; 3rd has 5 options: {1,3,5,7,9}
  let case4 := 4     -- 4th = 4 → 6th = 6; 3rd has 4 options: {2,4,6,8}
  let case6 := 5     -- 4th = 6 → 6th = 4; 3rd has 5 options: {1,3,5,7,9}
  let case8 := 2 * 4 -- 4th = 8 → 6th = 2 or 8; 3rd has 4 options: {2,4,6,8}

  have h : 3 * 4 * (case2 + case4 + case6 + case8) = 324 := by norm_num
  exact h
