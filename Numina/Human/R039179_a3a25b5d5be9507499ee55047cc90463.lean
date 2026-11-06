import Mathlib

open Int

/-
Proposition 1.5 states that for any real number \( x \), the following inequality holds: \( x - 1 < [x] \leq x \), where \( [x] \) denotes the greatest integer less than or equal to \( x \).
-/
theorem number_theory_4660 (x : ℝ) : x - 1 < floor x ∧ floor x ≤ x := by
  -- According to the definition of "floor," this proposition is clearly correct.
  constructor
  · have := Int.lt_floor_add_one x
    simp_all
  · exact Int.floor_le x
