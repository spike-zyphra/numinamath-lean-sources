import Mathlib

theorem number_theory_42021 : IsLeast {n | 0 < n ∧ n % 13 = 0 ∧ ∃ k l, n = 10 * k + 21 * l} 52 := by 
  constructor
  · -- Show that 52 is in the set
    refine ⟨by norm_num, by norm_num, ?_⟩
    use 1, 2
    all_goals norm_num
  · -- Show that 52 is the smallest element in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_mod, ⟨k, l, hn_eq⟩⟩
    by_contra h
    push_neg at h
    have h1 : n ≥ 13 := by 
      omega
    have h2 : n ≤ 39 := by
      omega
    interval_cases n <;> 
      omega