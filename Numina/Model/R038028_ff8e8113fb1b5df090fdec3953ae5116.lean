import Mathlib

theorem number_theory_185861 :
    IsGreatest {p | p.Prime ∧ ∃ n : ℕ, n ∈ Finset.Icc 100 999 ∧ (Nat.digits 10 n).length = 3 ∧
      (Nat.digits 10 n).toFinset.card = 3 ∧ p = n} 983 := by
  constructor
  · -- Show that 983 is in the set
    constructor
    · -- Show that 983 is prime
      norm_num
    · -- Use 983 as the witness n
      use 983
      all_goals norm_num
  · -- Show that 983 is the greatest
    intro p hp
    rcases hp with ⟨h_prime, ⟨n, hn1, hn2, hn3, hp⟩⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn1l, hn1r⟩
    by_contra h
    push_neg at h
    have h1 : n > 983 := by
      omega
    have h2 : n ≤ 999 := by
      omega
    interval_cases n <;> norm_num [hp] at *
    <;> norm_num at h_prime hp hn2 hn3 <;> try { contradiction }