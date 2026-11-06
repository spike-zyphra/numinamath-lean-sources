import Mathlib

theorem number_theory_7136 :
    IsLeast {n | n ≥ 1000 ∧ n % 9 = 0 ∧ (Nat.digits 10 n).length = 4 ∧
      (Nat.digits 10 n).toFinset.card = 4 ∧ ∀ d ∈ (Nat.digits 10 n), d ≠ 0} 1269 := by 
  constructor
  · -- Show that 1269 satisfies all conditions
    exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩ 
  · -- Show that 1269 is the smallest
    intro n hn
    rcases hn with ⟨h1000, hdiv9, h4, hcard, hnzero⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at h1000 hdiv9 h4 hcard hnzero <;> try { contradiction }
    <;> norm_num at *
    <;> try { contradiction }