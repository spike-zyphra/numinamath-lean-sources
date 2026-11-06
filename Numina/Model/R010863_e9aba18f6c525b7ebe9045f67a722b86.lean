import Mathlib

theorem number_theory_19483 :
    IsLeast {p | ∃n, 0 < n ∧ (n * (n + 1) * (n + 2) * (n + 3)) % 10 = 4 ∧ 1000 < n * (n + 1) * (n + 2) * (n + 3) ∧ p = n + (n + 1) + (n + 2) + (n + 3)} 30 := by
  constructor 
  · -- Show 30 is in the set.
    use 6 
    all_goals try { norm_num }
  · -- Show that 30 is the least element in the set
    intro p hp 
    rcases hp with ⟨n, hn_pos, hn_mod, hn_prod, hp_eq⟩ 
    by_contra h 
    push_neg at h 
    have h3 : n ≤ 26 := by 
      omega 
    interval_cases n <;> norm_num [hp_eq] at hn_mod hn_prod ⊢ 
    <;> try { omega }