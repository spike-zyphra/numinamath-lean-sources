import Mathlib

/-!
Define a recursive function `f : ℕ → ℕ → ℕ` based on the following:
For all positive integers `a, b`:

    f(a, b) =
      b                     if a > b
      f(2a, b)              if a ≤ b and f(2a, b) < a
      f(2a, b) - a          otherwise

We are to compute `f(1000, 3^2021)`, which is known to be 203.
-/


-- Use partial def since this is a non-structural recursion
partial def f : ℕ → ℕ → ℕ
  | a, b =>
    if a > b then
      b
    else
      let r := f (2 * a) b
      if r < a then r else r - a

-- Compute the value of f(1000, 3^2021)
def f_val : ℕ := f 1000 (3 ^ 2021)

#eval f_val  -- Expected output: 203

-- Theorem stating the expected result
theorem Number_Theory_610303 : f 1000 (3 ^ 2021) = 203 := by
  -- Evaluate directly via VM computation
  native_decide
