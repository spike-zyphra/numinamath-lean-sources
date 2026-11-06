import Mathlib

theorem number_theory_7088 : IsGreatest {n | ∃ k, 0 < k ∧ k % 6 = 2 ∧ k % 15 = 8 ∧ k % 60 = n} 38 := by 
  constructor
  · -- 38 is in the set
    use 38
    all_goals norm_num
  · -- Show that any n in the set is ≤ 38
    intro n hn
    rcases hn with ⟨k, hk_pos, hk1, hk2, hk3⟩
    omega