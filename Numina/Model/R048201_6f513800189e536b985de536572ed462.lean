import Mathlib

theorem number_theory_7021
    (n : ℕ)
    (hn : n > 0)
    (hdiv : 2 ∣ n ∧ 3 ∣ n ∧ 5 ∣ n ∧ 7 ∣ n)
    (hdigit : ∀ d ∈ Nat.digits 10 n, d ≠ 2 ∧ d ≠ 3 ∧ d ≠ 5 ∧ d ≠ 7) :
    IsLeast {n | n > 0 ∧ 2 ∣ n ∧ 3 ∣ n ∧ 5 ∣ n ∧ 7 ∣ n ∧ ∀ d ∈ Nat.digits 10 n, d ≠ 2 ∧ d ≠ 3 ∧ d ≠ 5 ∧ d ≠ 7} 840 := by
  constructor
  · -- Show that 840 is in the set.
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · native_decide
  · -- Show that 840 is the least such number.
    intro n hn
    rcases hn with ⟨hn_pos, h2, h3, h5, h7, hdigit⟩
    by_contra h
    push_neg at h
    have hdiv1 : n % 2 = 0 := by 
      omega
    have hdiv2 : n % 3 = 0 := by 
      omega
    have hdiv3 : n % 5 = 0 := by 
      omega
    have hdiv4 : n % 7 = 0 := by
      omega
    interval_cases n <;> norm_num at h2 h3 h5 h7 hdiv1 hdiv2 hdiv3 hdiv4 h <;> norm_num [Nat.digits, Nat.digitsAux] at hdigit ⊢ <;> try { contradiction }