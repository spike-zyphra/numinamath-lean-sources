import Mathlib

theorem number_theory_6216 : IsLeast {n : ℕ | n ≥ 1000 ∧ n ≤ 9999 ∧ Nat.gcd n 2136 = 267} 1335 := by 
  constructor
  · exact ⟨by norm_num, by norm_num, by norm_num⟩
  · intro n hn
    have ⟨hn1, hn2, h_gcd⟩ := hn
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at h_gcd