import Mathlib

open Nat

/- Find the least positive integer $n$ for which $2^n + 5^n - n$ is a multiple of $1000$. -/
theorem number_theory_42854 : IsLeast {n : ℕ | 0 < n ∧ 1000 ∣ (2^n + 5^n - n)} 797 := by
  -- Prove that 797 works
  constructor
  · constructor
    · positivity
    norm_num
  -- Prove that nothing else smaller works
  rw [lowerBounds]
  dsimp
  rintro a ⟨a_pos, ha⟩
  contrapose! ha
  interval_cases a
  all_goals
    norm_num