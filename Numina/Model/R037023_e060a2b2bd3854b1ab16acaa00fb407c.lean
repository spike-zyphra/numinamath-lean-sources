import Mathlib

theorem number_theory_180158 :
    IsLeast {n | 2 < n ∧ ∃ a b c d : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ n = a^2 + b^2 ∧ n = c^3 + d^3} 65 := by 
  constructor
  · -- Show 65 is in the set
    constructor
    · norm_num
    · -- Use a = 1, b = 8, c = 1, d = 4 to satisfy the condition
      use 1, 8, 1, 4
      all_goals norm_num
  · -- Show that 65 is minimal
    intro n hn
    rcases hn with ⟨hn1, a, b, c, d, ha, hb, hc, hd, h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : n < 65 := h
    have h4 : a ≤ 8 := by
      nlinarith [sq_nonneg (a : ℤ), sq_nonneg (b : ℤ), h1, h3]
    have h5 : b ≤ 8 := by
      nlinarith [sq_nonneg (a : ℤ), sq_nonneg (b : ℤ), h1, h3]
    have h6 : c ≤ 4 := by
      have h4_eq : c^3 + d^3 < 65 := by
        linarith [h1, h3]
      by_contra h8
      push_neg at h8
      have h8' : c ≥ 5 := by omega
      have h81 : c ^ 3 ≥ 125 := by
        have h811 : c ≥ 5 := h8'
        have h811' : (5 : ℕ) ^ 3 ≤ (c : ℕ) ^ 3 := by
          apply Nat.pow_le_pow_of_le_left
          omega
        omega
      have h1d3 : d ^ 3 ≥ 0 := by positivity
      nlinarith
    have h7 : d ≤ 4 := by
      have h4_eq : c^3 + d^3 < 65 := by
        linarith [h1, h3]
      by_contra h8
      push_neg at h8
      have h8d : d ≥ 5 := by omega
      have h81 : d ^ 3 ≥ 125 := by
        have h811 : d ≥ 5 := h8d
        have h811' : (5 : ℕ) ^ 3 ≤ (d : ℕ) ^ 3 := by
          apply Nat.pow_le_pow_of_le_left
          omega
        omega
      have h1d3 : c ^ 3 ≥ 0 := by positivity
      nlinarith
    interval_cases a <;> interval_cases b <;> try { 
      omega 
    }
    <;> interval_cases c <;> interval_cases d
    <;> omega