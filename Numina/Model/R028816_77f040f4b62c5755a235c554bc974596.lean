import Mathlib

theorem number_theory_15229 : IsLeast {n : ℕ | 0 < n ∧ (n % 10 ^ ((Nat.digits 10 n).length - 1) : ℕ) = (n / 29 : ℚ)} 725 := by
  constructor
  · -- Show 725 is in the set.
    constructor
    · -- Show 725 > 0.
      norm_num
    · -- Show the equation holds for 725.
      norm_num
  · -- Show no smaller positive integer is in the set.
    intro n hn
    rcases hn with ⟨hn_pos, hn_prop⟩
    by_contra h
    push_neg at h
    have h1 : n < 725 := h
    interval_cases n <;> norm_num at hn_prop ⊢
    <;> try { contradiction }