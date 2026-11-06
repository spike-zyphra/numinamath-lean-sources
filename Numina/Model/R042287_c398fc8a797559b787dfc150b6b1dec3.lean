import Mathlib

theorem algebra_18616 :
    {x : ℝ | (x / (2 * x - 1)) ^ 2 ≤ 9 ∧ x ≠ 1 / 2} = 
    {x : ℝ | x ≤ 3 / 7 ∨ x ≥ 3 / 5} := by 
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume x in first set
    rintro ⟨h1, h2⟩
    by_cases h : (2 * x - 1) > 0 
    · -- $2 * x - 1 > 0$
      have h3 : x > 1 / 2 := by linarith
      have h4 : (x / (2 * x - 1)) ^ 2 ≤ 9 := h1 
      have h5 : x ^ 2 ≤ 9 * (2 * x - 1) ^ 2 := by 
        have h6 : (x / (2 * x - 1)) ^ 2 ≤ 9 := h1 
        have h7 : (x / (2 * x - 1)) ^ 2 = x^2 / (2 * x - 1)^2 := by 
          field_simp 
        rw [h7] at h6 
        have h8 : x ^ 2 ≤ 9 * (2 * x - 1) ^ 2 := by
          have h9 : (2 * x - 1) ^ 2 > 0 := by nlinarith 
          apply (div_le_iff₀ h9).mp at h6 
          nlinarith 
        linarith
      have h6 : x ≥ 3 / 5 := by 
        nlinarith [sq_nonneg (x - 3 / 5), sq_nonneg (x - 3 / 7)]
      right 
      linarith 
    by_cases h' : (2 * x - 1) < 0 
    · -- Case $2 * x - 1 < 0$
      have h3 : x < 1 / 2 := by linarith 
      have h4 : (x / (2 * x - 1)) ^ 2 ≤ 9 := h1 
      have h5 : x ^ 2 ≤ 9 * (2 * x - 1) ^ 2 := by 
        have h6 : (x / (2 * x - 1)) ^ 2 ≤ 9 := h1 
        have h7 : (x / (2 * x - 1)) ^ 2 = x^2 / (2 * x - 1)^2 := by 
          field_simp 
        rw [h7] at h6 
        have h8 : (2 * x - 1) ^ 2 > 0 := by 
          nlinarith 
        have h7' : x^2 / (2 * x - 1)^2 ≤ 9 := h6 
        have h9 : x ^ 2 ≤ 9 * (2 * x - 1) ^ 2 := by 
          have h58 : (2 * x - 1) ^ 2 > 0 := by nlinarith 
          apply (div_le_iff₀ h58).mp at h7'
          nlinarith 
        linarith
      have h7 : x ≤ 3 / 7 := by 
        nlinarith [sq_nonneg (x - 3 / 7), sq_nonneg ((2 * x - 1)), sq_pos_of_neg (show (2 * x - 1) < 0 by linarith)]
      left 
      linarith 
    have h3 : (2 * x - 1) = 0 := by linarith 
    have h4 : x = 1 / 2 := by linarith 
    contradiction 
  · -- Assume x in second set 
    rintro (h | h)
    · -- Case x ≤ 3/7
      have h1 : x ≤ 3 / 7 := h 
      have h2 : (2 * x - 1) < 0 := by nlinarith 
      have h3 : (x / (2 * x - 1)) ^ 2 ≤ 9 := by
        have h4 : x ^ 2 ≤ 9 * (2 * x - 1) ^ 2 := by nlinarith [sq_nonneg (x - 3 / 5), sq_nonneg (x - 3 / 7)]
        have h5 : (x / (2 * x - 1)) ^ 2 = x^2 / (2 * x - 1)^2 := by 
          field_simp 
        have h58 : (2 * x - 1) ^ 2 > 0 := by nlinarith 
        rw [h5]
        have h7 : x^2 / (2 * x - 1)^2 ≤ 9 := by
          apply (div_le_iff₀ h58).mpr 
          nlinarith 
        linarith 
      have h4 : x ≠ 1 / 2 := by 
        nlinarith 
      tauto 
    · -- Case x ≥ 3/5
      have h1 : x ≥ 3 / 5 := h 
      have h2 : (2 * x - 1) > 0 := by nlinarith
      have h3 : (x / (2 * x - 1)) ^ 2 ≤ 9 := by
        have h4 : x ^ 2 ≤ 9 * (2 * x - 1) ^ 2 := by nlinarith [sq_nonneg (x - 3 / 5), sq_nonneg (x - 3 / 7)]
        have h5 : (x / (2 * x - 1)) ^ 2 = x^2 / (2 * x - 1)^2 := by 
          field_simp 
        have h58 : (2 * x - 1) ^ 2 > 0 := by nlinarith
        rw [h5]
        have h7 : x^2 / (2 * x - 1)^2 ≤ 9 := by 
          apply (div_le_iff₀ h58).mpr
          nlinarith 
        linarith 
      have h4 : x ≠ 1 / 2 := by 
        nlinarith 
      tauto