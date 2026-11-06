import Mathlib

theorem algebra_19908 :
    IsLeast {p : ℕ | p.Prime ∧ ∃ m n, p = m^2 + n^2 ∧ m > 0 ∧ n > 0 ∧ m ≠ n} 5 := by
  constructor
  · -- Show 5 is in the set
    constructor
    · -- Show 5 is prime
      norm_num
    · -- Show there exist m and n such that 5 = m^2 + n^2 and m > 0, n > 0, m ≠ n
      use 1, 2
      all_goals norm_num
  · -- Show no number less than 5 is in the set
    intro p hp
    rcases hp with ⟨h_prime, m, n, heq, hm, hn, hneq⟩
    by_contra h
    push_neg at h
    have h1 : p < 5 := by linarith
    have h2 : m ≤ 2 := by
      by_contra h3
      push_neg at h3
      have h3' : m ≥ 3 := by omega
      have h5 : m^2 ≥ 9 := by
        have : m ≥ 3 := h3'
        nlinarith
      have h6 : p ≥ 9 := by
        nlinarith [heq, h5, show n > 0 by omega]
      omega
    have h3 : n ≤ 2 := by
      by_contra h4
      push_neg at h4
      have h4' : n ≥ 3 := by omega
      have h5 : n^2 ≥ 9 := by
        have : n ≥ 3 := h4'
        nlinarith
      have h6 : p ≥ 9 := by
        nlinarith [heq, h5, show m > 0 by omega]
      omega
    interval_cases m <;> interval_cases n
      <;> norm_num [heq] at *
      <;> norm_num at h_prime hneq
      <;> all_goals try { contradiction }