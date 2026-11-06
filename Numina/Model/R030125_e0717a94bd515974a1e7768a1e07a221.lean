import Mathlib

theorem number_theory_55601 : IsGreatest {x | ∃ n, x = 2018 % n ∧ 1 ≤ n ∧ n ≤ 1000} 672 := by
  constructor
  · -- Show 672 is in the set
    use 673
    all_goals norm_num
  · -- Show there is no greater element in the set
    intro x hx
    rcases hx with ⟨n, hn1, hn2, hn3⟩
    by_contra h
    push_neg at h
    have h1 : x = 2018 % n := by
      exact_mod_cast hn1
    rw [h1] at h
    have h3 : n ≤ 1000 := by omega
    interval_cases n <;> norm_num at h hn1
    all_goals omega