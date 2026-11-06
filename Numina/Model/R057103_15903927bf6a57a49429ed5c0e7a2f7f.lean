import Mathlib

theorem number_theory_195693 (R : ℕ) (hR : R > 0) :
    R^2000 < 5^3000 ↔ R ≤ 11 := by
  constructor
  · -- Forward: if R^2000 < 5^3000, then R ≤ 11
    intro h
    by_contra h'
    push_neg at h'
    have h1 : R ≥ 12 := by omega
    have h2 : R ^ 2000 ≥ 12 ^ 2000 := by
      have h3 : R ≥ 12 := h1
      have h4 : R ^ 2000 ≥ 12 ^ 2000 := by
        apply Nat.pow_le_pow_of_le_left
        omega
      linarith
    have h5 : (12 : ℕ) ^ 2000 > 5 ^ 3000 := by
      norm_num
    have h6 : R ^ 2000 ≥ (12 : ℕ) ^ 2000 := by 
      linarith
    have h7 : R ^ 2000 > 5 ^ 3000 := by
      linarith
    linarith
  · -- Backward: if R ≤ 11, then R^2000 < 5^3000
    intro h
    have h1 : R ≤ 11 := h
    have h2 : R ^ 2000 < 5 ^ 3000 := by
      have h3 : R ≤ 11 := h1
      have h4 : R ^ 2000 ≤ 11 ^ 2000 := by
        have h5 : R ≤ 11 := h3
        have h6 : R ^ 2000 ≤ 11 ^ 2000 := by
          apply Nat.pow_le_pow_of_le_left
          omega
        linarith
      have h7 : 11 ^ 2000 < 5 ^ 3000 := by
        norm_num
      have h8 : R ^ 2000 < 5 ^ 3000 := by
        linarith
      linarith
    linarith