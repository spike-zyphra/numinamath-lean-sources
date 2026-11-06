import Mathlib

open scoped BigOperators

/- Let f(x)=x^2-2, and let f^n denote the function f applied n times. Compute the remainder when f^24(18) is divided by 89. -/

-- Define f(x)=x^2-2, the return value is set to be the remainder divided by 89
def f : ZMod 89 → ZMod 89 := fun x => x * x - 2
-- Define an iterator
def iterator (g : a → a) : ℕ → a → a
| 0,     x => x
| n + 1, x => iterator g n (g x)
-- Then the result can be calculated
theorem algebra_609330 : iterator f 24 18 = 47 := by
  native_decide
