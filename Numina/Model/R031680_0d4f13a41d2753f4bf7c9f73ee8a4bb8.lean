import Mathlib

theorem number_theory_252784 : IsGreatest {n | ∃ k : ℕ, n = 9984 - 8 * k ∧ (Nat.digits 10 n).length = 4 ∧
    (Nat.digits 10 n).toFinset.card = 4} 9872 := by

  constructor
  · -- Show 9872 is in the set
    use 14
    all_goals native_decide
  · -- Show 9872 is greatest in the set
    intro n hn
    rcases hn with ⟨k, h1, h2, h3⟩

    by_contra h
    push_neg at h

    have h4 : n > 9872 := h
    have h5 : k < 14 := by
      omega

    interval_cases k <;> norm_num [h1] at h2 h3 ⊢
      <;> omega