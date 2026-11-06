import Mathlib

/- What is the least positive integer $n$ such that $4125$ is a factor of $n!$? -/
theorem number_theory_17032 :
    IsLeast {n : ℕ | 0 < n ∧ 4125 ∣ Nat.factorial n} 15 := by
  refine' ⟨by decide, fun n hn => _⟩
  norm_num at hn
  apply le_of_not_gt
  intro H
  revert hn
  revert n
  decide