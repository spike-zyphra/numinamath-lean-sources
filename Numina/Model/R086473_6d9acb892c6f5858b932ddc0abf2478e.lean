import Mathlib

theorem algebra_264572 (n : ℕ) : 3 * (n ^ 2007) < 3 ^ 4015 ↔ n ≤ 8 := by
  constructor
  · -- Assume 3 * (n ^ 2007) < 3 ^ 4015, prove n ≤ 8
    intro h 
    by_contra h1
    push_neg at h1 
    have h2 : n ≥ 9 := by omega
    have h3 : n ^ 2007 ≥ 9 ^ 2007 := by 
      have h4 : n ≥ 9 := h2
      have h5 : n ^ 2007 ≥ 9 ^ 2007 := by 
        apply Nat.pow_le_pow_of_le_left 
        all_goals omega 
      linarith 
    have h6 : 3 * (n ^ 2007) ≥ 3 * (9 ^ 2007) := by 
      nlinarith [h3] 
    have h7 : 3 * (9 ^ 2007) = 3 ^ 4015 := by
      norm_num 
    linarith 
  · -- Assume n ≤ 8, prove 3 * (n ^ 2007) < 3 ^ 4015
    intro h 
    have h1 : n ≤ 8 := h 
    have h2 : n ^ 2007 < 9 ^ 2007 := by 
      have h3 : n ≤ 8 := h1 
      have h4 : n < 9 := by omega 
      have h5 : n ^ 2007 < 9 ^ 2007 := by 
        apply Nat.pow_lt_pow_left 
        all_goals omega 
      linarith 
    have h6 : 3 * (n ^ 2007) < 3 * (9 ^ 2007) := by 
      nlinarith [h2] 
    have h7 : 3 * (9 ^ 2007) = 3 ^ 4015 := by
      norm_num 
    linarith