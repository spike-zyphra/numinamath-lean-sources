import Mathlib

/-
1. Show that \(3\) divides \(99\), \(5\) divides \(145\), \(7\) divides \(343\), and \(888\) divides \(0\).
-/
theorem number_theory_4671 : 3 ∣ 99 ∧ 5 ∣ 145 ∧ 7 ∣ 343 ∧ 888 ∣ 0 := by
  -- According to the definition of divisibility, we can directly prove this proposition to be correct through calculation.
  split_ands <;> norm_num
