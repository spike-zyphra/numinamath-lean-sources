import Mathlib

theorem number_theory_250756 (a b : ℕ) (_ : 0 < a) (h₀ : 0 < b)
    (h₁ : 96 * a ^ 2 = b ^ 3) :
    a ≥ 12 := by
  by_contra h
  push_neg at h
  have h2 : a < 12 := h
  have h3 : b ≤ 22 := by
    by_contra h4
    push_neg at h4
    have h4 : b ≥ 23 := by omega
    have h5 : a ≤ 11 := by linarith
    have h7 : 96 * a ^ 2 < 23 ^ 3 := by
      have h8 : a ≤ 11 := by linarith
      have h9 : a ^ 2 ≤ 121 := by nlinarith
      nlinarith
    have h8 : b ^ 3 ≥ 23 ^ 3 := by
      have h9 : b ≥ 23 := by linarith
      have h10 : b ^ 3 ≥ 23 ^ 3 := by
        apply Nat.pow_le_pow_of_le_left
        all_goals linarith
      linarith
    nlinarith [h₁, h7, h8]
  interval_cases b <;> try { 
    have h4 : a < 12 := h
    interval_cases a <;> omega 
  }