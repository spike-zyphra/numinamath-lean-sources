import Mathlib

open List

/- Question: In the expression a / b + c / d + e / f each letter is replaced by a different digit from {1, 2, 3, 4, 5, 6}. Show that the largest possible value of this expression is 59/6. -/

-- a, b, c, d, e, f are different values from 1-6
def choices : List ℚ := [1, 2, 3, 4, 5, 6]
-- Define the expression
def expression : List ℚ → ℚ
| [a, b, c, d, e, f] => a / b + c / d + e / f
| _                  => 0
-- Evaluate all the possible values
def values : List ℚ := (choices.permutations).map expression
-- Find out the maximum
def max_value : ℚ := values.foldl (fun acc x => max acc x) 0
theorem algebra_271198 : max_value = 59 / 6 := by
  dsimp [max_value, values, expression, choices]
  native_decide
