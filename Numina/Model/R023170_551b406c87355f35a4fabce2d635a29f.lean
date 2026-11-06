import Mathlib

theorem other_156526 (h : ∃ m1 m2 : ℝ, m1 = 1 ∧ m2 = 1 ∧ (100 - 0) * m1 = (60 - 0) * m2) :
    IsGreatest {x | ∃ m1 m2 : ℝ, m1 = 1 ∧ m2 = 1 ∧ (100 - 0) * m1 = (x - 0) * m2} 63.2 := by
  rcases h with ⟨m1, m2, hm1, hm2, heq⟩
  rw [hm1, hm2] at heq
  norm_num at heq
  all_goals
    norm_num [IsGreatest, upperBounds]
    <;> try { linarith }
    <;> norm_num