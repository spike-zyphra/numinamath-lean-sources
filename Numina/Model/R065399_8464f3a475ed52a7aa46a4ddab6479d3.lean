import Mathlib

theorem number_theory_19351 :
    IsGreatest {x | ∃ n, x = n^2 ∧ x < 225 ∧ 9 ∣ x} 144 := by
  constructor
  · -- Show 144 is in the set
    use 12
    all_goals norm_num
  · -- Show that 144 is the greatest element in the set
    intro x hx
    rcases hx with ⟨n, rfl, hn1, hn2⟩
    by_contra h
    push_neg at h
    have h1 : n ≤ 14 := by nlinarith
    interval_cases n <;> norm_num at hn1 hn2 ⊢ <;> omega