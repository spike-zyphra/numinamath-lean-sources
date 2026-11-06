import Mathlib

def isBold (n : ℕ) : Prop :=
  n.divisors.card = 8 ∧ ∑ d ∈ n.divisors, d = 3240

/- determine -/ abbrev solution : ℕ := 1614

theorem number_theory_36742 :
    IsLeast {n | 0 < n ∧ isBold n} solution := by
  constructor 
  · -- Show 1614 is in the set {n | 0 < n ∧ isBold n}
    constructor
    · -- Show 0 < 1614
      all_goals norm_num [solution]
    · -- Show isBold 1614
      unfold isBold
      constructor
      · -- Show the number of divisors is 8
        native_decide
      · -- Show the sum of divisors is 3240
        native_decide
  · -- Show it's minimal
    intro n hn
    have ⟨hn_pos, hn_bold⟩ := hn
    by_contra h 
    push_neg at h
    have h1 : n < 1614 := h 
    rcases hn_bold with ⟨h_card, h_sum⟩
    have : n < 1614 := h1 
    have : n.divisors.card ≠ 8 ∨ ∑ d ∈ n.divisors, d ≠ 3240 := by
      interval_cases n <;> try { native_decide }
    cases this with
    | inl h3 => 
      omega -- This shows contradiction between h_card and h3
    | inr h3 => 
      omega -- This shows contradiction between h_sum and h3