import Mathlib

/-
If $ x $ and $ y $ are real numbers, then the sum of the maximum and minimum of $ x $ and $ y $ is equal to the sum of $ x $ and $ y $. In mathematical terms, this can be expressed as $ \max(x, y) + \min(x, y) = x + y $.
-/
theorem number_theory_4555
    (x y : ℝ) :
    max x y + min x y = x + y := by
-- consider two cases based on the relationship between $ x $ and $
-- **Case 1:** If $ x \geq y $, then by definition, the minimum of $ x $ and $ y $ is $ y $ (i.e., $ \min(x, y) = y $) and the maximum is $ x $ (i.e., $ \max(x, y) = x $). Therefore, we can calculate:
-- $$
-- \max(x, y) + \min(x, y) = x + y.
-- $$
-- **Case 2:** If $ x < y $, then the minimum of $ x $ and $ y $ is $ x $ (i.e., $ \min(x, y) = x $) and the maximum is $ y $ (i.e., $ \max(x, y) = y $). In this case, we have:
-- $$
-- \max(x, y) + \min(x, y) = y + x = x + y.
-- $$
-- In both cases, we find that $ \max(x, y) + \min(x, y) = x + y $. Thus, the lemma is proven.
  cases le_or_lt y x <;> simp
