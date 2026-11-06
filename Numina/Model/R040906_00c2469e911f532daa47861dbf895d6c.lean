import Mathlib

open Finset

theorem number_theory_63105 {P : ℕ → ℕ}
    (hP : ∀ n, P n = ∏ d ∈ n.divisors, d) :
    IsLeast {n | 0 < n ∧ P (P (P n)) > 10 ^ 12} 6 := by
  constructor
  · -- First, show 6 is in the set
    constructor
    · norm_num
    · -- Show P(P(P 6)) > 10^12
      rw [hP, hP, hP]
      native_decide
  · -- Now prove it is minimal
    intro n hn
    rcases hn with ⟨hn_pos, hn_ineq⟩
    by_contra h
    push_neg at h
    have h1 : n < 6 := h
    interval_cases n <;> simp [hP] at hn_ineq ⊢ <;> try { contradiction }
    <;> native_decide