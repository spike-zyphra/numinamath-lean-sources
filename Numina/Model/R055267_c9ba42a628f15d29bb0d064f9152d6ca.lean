import Mathlib

theorem number_theory_19146 : IsGreatest {n : ℕ | ∃ k, n = k % 3 ∧ k ≥ 0} 2 := by 
  constructor 
  · -- To prove 2 is in the set, we can choose k = 2.
    use 2
    all_goals simp
  · -- To prove 2 is greatest in the set, take any n in the set.
    intro n hn
    rcases hn with ⟨k, rfl, hk⟩
    -- When k is a natural number, and k ≥ 0, then k % 3 can be 0, 1, 2
    -- So k % 3 ≤ 2.
    have : k % 3 < 3 := by 
      apply Nat.mod_lt 
      norm_num 
    omega