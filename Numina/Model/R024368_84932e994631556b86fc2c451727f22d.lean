import Mathlib

theorem number_theory_7478 :
    IsLeast {n | (n.primeFactors.card = 4) ∧ ∃ k, n = (6 * k + 1) * (6 * k + 5)} 8645 := by
  constructor
  · -- Show 8645 is in the set.
    constructor
    · native_decide
    · use 15
      all_goals
      native_decide
  · -- Show that 8645 is the least such number.
    intro n hn
    rcases hn with ⟨h1, ⟨k, hk⟩⟩
    by_contra h
    push_neg at h
    have h2 : n < 8645 := by
      linarith
    have h3 : k ≤ 14 := by
      by_contra h4
      push_neg at h4
      have h4' : k ≥ 15 := by omega
      have h5 : (6 * k + 1) * (6 * k + 5) ≥ 8645 := by
        have h6 : k ≥ 15 := h4'
        have h7 : (6 * k + 1) ≥ 91 := by
          omega
        have h8 : (6 * k + 5) ≥ 95 := by
          omega
        have h9 : (6 * k + 1) * (6 * k + 5) ≥ 91 * 95 := by
          nlinarith [show (6 * k + 1) ≥ 91 by omega, show (6 * k + 5) ≥ 95 by omega]
        have h10 : (91 * 95 : ℕ) = 8645 := by norm_num
        linarith
      nlinarith [show (6 * k + 1) * (6 * k + 5) = n by linarith [hk], h2, h5]
    interval_cases k <;> norm_num [hk] at *
    all_goals
      norm_num [Nat.primeFactors, Nat.primeFactorsList] at h1 ⊢ <;> try { all_goals contradiction }