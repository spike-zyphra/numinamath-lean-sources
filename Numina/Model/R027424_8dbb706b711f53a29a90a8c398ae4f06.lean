import Mathlib


open Nat


lemma lemma_1 (n : ℕ) (h1 : 10 ≤ n) (h2 : n ≤ 99) :
    (Nat.digits 10 n).length = 2 ∧ (Nat.digits 10 n).toFinset.card = 1 ↔
    (Nat.digits 10 n).headI = (Nat.digits 10 n).tail.headI := by
  constructor
  ·
    intro h
    rcases h with ⟨h_len, h_card⟩
    interval_cases n <;> norm_num at h_len h_card ⊢
  ·
    intro h
    interval_cases n <;> norm_num at h ⊢


theorem number_theory_7063 :
    IsLeast {p | p.Prime ∧ ∃ k, (Nat.digits 10 p).contains k ∧ (Nat.digits 10 p).count k ≥ 2} 11 := by
  constructor
  · -- Show 11 is in the set
    constructor
    · norm_num
    · use 1
      native_decide
  · -- Show there is no smaller element in the set
    intro p hp
    rcases hp with ⟨h_prime, ⟨k, hk1, hk2⟩⟩
    by_contra h
    push_neg at h
    interval_cases p <;> norm_num at h_prime
    <;> try { contradiction }
    <;> try { 
      simp_all [Nat.digits, Nat.digitsAux]
      all_goals try { 
        omega
      }
    }