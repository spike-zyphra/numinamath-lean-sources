import Mathlib

theorem number_theory_229320 : IsGreatest {x | ∃ n, x = 2015 % n ∧ 1 ≤ n ∧ n ≤ 1000} 671 := by
  constructor
  · -- Show that 671 is in the set. 
    use 672
    all_goals norm_num
  · -- Show that 671 is greatest in the set.
    intro x hx
    rcases hx with ⟨n, hx1, hn1, hn2⟩
    by_contra h
    push_neg at h
    have h1 : 2015 % n > 671 := by
      omega
    interval_cases n <;> norm_num at hx1 ⊢ <;> omega