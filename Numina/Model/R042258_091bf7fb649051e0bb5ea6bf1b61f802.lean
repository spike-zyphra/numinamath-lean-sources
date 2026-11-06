import Mathlib

theorem number_theory_200778 : IsLeast {p | p.Prime ∧ p ∣ 101^303 + 301^101} 2 := by
  constructor
  · -- Show 2 is in the set.
    constructor
    · norm_num
    · norm_num
  · -- Show there is no smaller element in the set.
    intro p hp
    rcases hp with ⟨h_prime, h_div⟩
    by_contra h
    push_neg at h
    have h1 : p < 2 := h
    interval_cases p <;> norm_num at h_prime h_div ⊢