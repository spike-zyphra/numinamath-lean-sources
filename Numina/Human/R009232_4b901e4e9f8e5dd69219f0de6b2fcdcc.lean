import Mathlib

/- What is the value of the expression \([a] + [-a]\) when \(a\) is a real number, where \([x]\) denotes the greatest integer less than or equal to \(x\)?-/
theorem number_theory_4868 (x : ℝ) (n : ℤ) : ⌊x + n⌋ = ⌊x⌋ + n :=
  -- exact `Int.floor_add_int` in Mathlib
  Int.floor_add_int x n
