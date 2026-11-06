import Mathlib

theorem number_theory_65639 :
    ∑ n in (Finset.Ico 0 2023).filter (fun n => IsSquare (2 * n ^ 2 + 3 * n)), n = 444 := by 
  native_decide