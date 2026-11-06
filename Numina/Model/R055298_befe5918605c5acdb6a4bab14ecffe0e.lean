import Mathlib

theorem number_theory_224941 (n : ℕ) :
    ∃ p, Nat.Prime p ∧ p^3 = 2^n + n^2 + 25 ↔ n = 6 := by
  use 5
  constructor
  · -- Assume Nat.Prime p ∧ p^3 = 2^n + n^2 + 25
    intro h
    rcases h with ⟨h_prime, h_eq⟩
    have h1 : n ≤ 6 := by
      by_contra h2
      push_neg at h2
      have h2' : n ≥ 7 := by linarith
      have h3 : 2^n + n^2 + 25 > 125 := by
        have h4 : n ≥ 7 := h2'
        have h5 : 2^n ≥ 128 := by
          have h6 : n ≥ 7 := h4
          have h7 : 2^n ≥ 128 := by
            have h8 : 2^7 = 128 := by norm_num
            have h9 : n ≥ 7 := h6
            have h10 : 2^n ≥ 2^7 := by
              apply Nat.pow_le_pow_of_le_right
              · norm_num
              · linarith
            linarith [h8, h10]
          linarith
        have h11 : n^2 ≥ 49 := by
          nlinarith [h4]
        nlinarith
      have h4 : 2^n + n^2 + 25 = 125 := by
        linarith [h_eq]
      linarith [h3, h4]
    interval_cases n <;> norm_num at h_eq <;> tauto
  · -- Conversely, assume n = 6
    intro h_eq
    rw [h_eq]
    constructor
    · -- Show that 5 is prime (trivial)
      norm_num
    · -- Show that 5^3 = 2^6 + 6^2 + 25
      norm_num