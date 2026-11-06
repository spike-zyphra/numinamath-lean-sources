import Mathlib

  theorem number_theory_19034 :
    IsLeast {n : ℕ | ∃ k, k > 0 ∧ n = k^3 ∧ ∃ m : ℤ, n = m + (m + 1) + (m + 2)} 27 := by
  constructor
  · -- First part: 27 is in the set
    use 3
    constructor
    · norm_num
    constructor
    · norm_num
    · refine ⟨8, by norm_num⟩
  · -- Second part: no smaller element is in the set
    intro n hn
    rcases hn with ⟨k, hk, hn_eq, m, hm⟩
    by_contra h
    push_neg at h
    have h1 : k^3 < (27 : ℕ) := by
      have h_eq : n = k^3 := by linarith
      omega
    have hk2 : k ≤ 2 := by
      by_contra h2
      push_neg at h2
      have h3 : k ≥ 3 := by linarith
      have h4 : k^3 ≥ 27 := by
        have h2 : k ≥ 3 := h3
        have h4 : k ^ 3 ≥ 3^3 := by
          apply Nat.pow_le_pow_of_le_left
          linarith
        norm_num at h4 ⊢
        linarith
      omega
    have hk1 : k ≤ 2 := by linarith
    interval_cases k <;> norm_num at hn_eq
    <;> norm_num [hn_eq] at hm ⊢
    all_goals omega