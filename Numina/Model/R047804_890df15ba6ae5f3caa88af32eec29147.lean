import Mathlib
theorem algebra_611196 (x : ℝ) : x ^ 4 + (2 - x) ^ 4 = 34 ↔ x = 1 + √2 ∨ x = 1 - √2:= by
  constructor
  · -- Forward: if x^4 + (2-x)^4 = 34 then x = 1 ± √2
    intro h
    have h1 : x ^ 4 + (2 - x) ^ 4 = 2 * ((x - 1) ^ 4) + 12 * ((x - 1) ^ 2) + 2 := by
      ring_nf
    rw [h1] at h
    have h2 : ((x - 1) ^ 2) ^ 2 + 6 * ((x - 1) ^ 2) - 16 = 0 := by
      nlinarith
    have h3 : ((x - 1) ^ 2) = 2 := by
      nlinarith [sq_nonneg ((x - 1) ^ 2 - 2), sq_nonneg ((x - 1) ^ 2 + 8)]
    have h4 : (x - 1) ^ 2 - 2 = 0 := by
      linarith
    have h5 : (x - 1) ^ 2 = 2 := by
      linarith
    have h6 : x - 1 = Real.sqrt 2 ∨ x - 1 = -Real.sqrt 2 := by
      have h7 : (x - 1) ^ 2 = (Real.sqrt 2) ^ 2 := by
        rw [h5]
        <;> norm_num
        <;> ring_nf <;> norm_num
      have : x - 1 = Real.sqrt 2 ∨ x - 1 = -Real.sqrt 2 := by
        apply eq_or_eq_neg_of_sq_eq_sq
        norm_num
        linarith [h7]
      assumption
    cases h6 with
    | inl h8 =>
      left
      linarith
    | inr h9 =>
      right
      linarith
  · -- Reverse: x = 1 ± √2 then x^4 + (2-x)^4 = 34
    rintro (h | h)
    · -- x = 1 + √2
      rw [h]
      have h7 : (1 + Real.sqrt 2 : ℝ) ^ 4 + (2 - (1 + Real.sqrt 2) : ℝ) ^ 4 = 34 := by
        have h7 : (2 - (1 + Real.sqrt 2) : ℝ) = (1 - Real.sqrt 2 : ℝ) := by nlinarith
        rw [h7]
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 ^ 2 - 2)]
      linarith
    · -- x = 1 - √2
      rw [h]
      have h8 : (1 - Real.sqrt 2 : ℝ) ^ 4 + (2 - (1 - Real.sqrt 2) : ℝ) ^ 4 = 34 := by
        have h8 : (2 - (1 - Real.sqrt 2) : ℝ) = (1 + Real.sqrt 2 : ℝ) := by nlinarith
        rw [h8]
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 ^ 2 - 2)]
      linarith