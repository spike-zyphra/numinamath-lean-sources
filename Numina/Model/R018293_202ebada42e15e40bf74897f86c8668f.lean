import Mathlib

theorem number_theory_288678 :
    IsLeast {n | n ≥ 1000 ∧ n < 10000 ∧ 5 ∣ n ∧ 9 ∣ n ∧ ∀ d ∈ Nat.digits 10 n, Even d} 2880 := by
  constructor
  · -- Show 2880 is in the set
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · native_decide
  · -- Show no smaller element is in the set
    intro n hn
    rcases hn with ⟨h1000, h10000, h5, h9, heven⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at h5 h9 h1000 h10000
    <;> norm_num [Nat.even_iff] at heven
    <;> try { contradiction }
    <;> omega