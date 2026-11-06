import Mathlib

/- What is the least positive integer $n$ such that $80325$ divides $n!$? -/
theorem number_theory_18982 :
    IsLeast {n | 0 < n ∧ 80325 ∣ Nat.factorial n} 17 := by 
  refine ⟨by decide, ?_⟩
  intro n hn
  norm_num at hn
  apply le_of_not_gt
  intro h
  revert hn
  revert n
  decide