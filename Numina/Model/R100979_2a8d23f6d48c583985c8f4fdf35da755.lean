import Mathlib

theorem number_theory_9786 :
    IsLeast {n | n ≥ 100 ∧ n.primeFactors.card = 3} 102 := by
  constructor
  · -- Show that 102 is in the set, so we check its prime factors
    constructor
    · norm_num
    · native_decide
  · -- Show no smaller element is in the set
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [Nat.primeFactors, Nat.primeFactorsList] at hn2 ⊢ <;>
      try { 
        contradiction
      }
    <;> try { 
      exfalso <;> norm_num at hn2 ⊢ <;> try contradiction <;> try trivial
    }
    <;> try { 
      have h100 : (Nat.primeFactors (100 : ℕ)).card ≠ 3 := by
        native_decide
      contradiction
    }
    <;> try { 
      have h101 : (Nat.primeFactors (101 : ℕ)).card ≠ 3 := by
        native_decide
      contradiction
    }