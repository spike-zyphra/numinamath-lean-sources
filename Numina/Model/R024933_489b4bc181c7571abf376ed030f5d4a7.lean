import Mathlib

theorem number_theory_189071 :
    IsLeast {n | n ≥ 1000 ∧ n ≤ 9999 ∧ ∃ k l, n = (k + l)^2 ∧ k = (n / 100) % 100 ∧ l = n % 100} 2025 := by
  constructor
  · -- Show 2025 is in the set.
    constructor
    · norm_num
    constructor
    · norm_num
    · use 20, 25
      all_goals norm_num
  · -- Show no smaller element is in the set.
    intro n hn
    rcases hn with ⟨h1000, h9999, k, l, h_eq, hk, hl⟩
    by_contra h
    push_neg at h
    have h2 : n < 2025 := h
    have h3 : k = n / 100 := by
      omega
    have h4 : l = n % 100 := by
      omega
    rw [h3] at h_eq
    rw [h4] at h_eq
    interval_cases n <;> norm_num at h_eq <;> omega