import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_599254 :
  IsGreatest {z : ℝ | ∃ x y, z = abs (x + 2 * y - 4) ∧ x - y + 2 ≥ 0 ∧ x + y - 4 ≥ 0 ∧ 2 * x - y - 5 ≤ 0} 21 := by
  constructor
  · -- Show that 21 is attained, with witness (7, 9)
    use 7, 9
    norm_num [abs_of_nonneg]
    <;> norm_num
    all_goals norm_num
  · -- Show that any value in the set is ≤ 21
    intro z hz
    rcases hz with ⟨x, y, h_eq, hx1, hx2, hx3⟩
    have h4 : abs (x + 2 * y - 4) ≤ 21 := by
      cases' abs_cases (x + 2 * y - 4) with h h
      · -- Case where x + 2y - 4 ≥ 0, so abs = value
        nlinarith
      · -- Case where x + 2y - 4 < 0, so abs = -value
        nlinarith
    linarith