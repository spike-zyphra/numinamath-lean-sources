import Mathlib

theorem inequalities_50867 :
    ∑ x in (Finset.Ico 1 359).filter (fun x => 1 + 8 * x ≤ 358 - 2 * x ∧ 358 - 2 * x ≤ 6 * x + 94), x = 102 := by 
  native_decide