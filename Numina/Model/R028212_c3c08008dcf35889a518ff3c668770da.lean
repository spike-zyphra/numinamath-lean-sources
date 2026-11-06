import Mathlib

theorem number_theory_15085 : IsLeast {n : ℕ | Nat.lcm 45 n / Nat.gcd 45 n = 33} 165 := by
  constructor
  · -- Show 165 is in the set
    norm_num
  · -- Show there's no smaller element in the set
    intro n hn
    have h : Nat.lcm 45 n / Nat.gcd 45 n = 33 := hn
    by_contra h'
    push_neg at h'
    interval_cases n <;> norm_num at h <;> all_goals try { tauto }
  all_goals try { try { tauto } }
  all_goals try { contradiction }
  <;> norm_num at *
  <;> try { omega }
  <;> contradiction