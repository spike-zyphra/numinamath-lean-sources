import Mathlib
open Real
/- Antonette gets 70% on a 10-problem test, 80% on a 20-problem test and 90% on
a 30-problem test. If the three tests are combined into one 60-problem test, which
percent is closest to her overall score?
(A) 40  (B) 77 (C) 80 (D) 83  (E) 87 -/
theorem algebra_95958 (a b c : ℕ) (ha : a = 70) (hb : b = 80) (hc : c = 90)
(h : a * 10 + b * 20 + c * 30 = 60 * x) :
x = 83 := by
  -- substitute the variables and then compute the result
  subst_vars
  omega