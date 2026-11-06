import Mathlib

open Nat Set

theorem inequalities_180071 :
    IsGreatest {x | ∃ a b, x = a + 2 * b ∧ 3 * a - 2 * b ≤ 10 ∧ 3 * a + 8 * b ≤ 25} 7 := by
  constructor
  · -- Show that 7 can be obtained with a = 3 and b = 2
    use 3, 2
    all_goals omega
  · -- Show that any s in the set is ≤ 7
    intro s hs
    rcases hs with ⟨a, b, h_eq, h1, h2⟩
    omega