import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_26340 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
  (M : Set ℝ) (hM : M = {x | ∃ u v : ℝ, u > 0 ∧ v > 0 ∧ u + v = 1 ∧ x = a * u + b * v}) :
  (2 * a * b / (a + b) ∈ M) ∧ (Real.sqrt (a * b) ∈ M) := by

  have h1 : 2 * a * b / (a + b) ∈ M := by 
    rw [hM]
    use b / (a + b), a / (a + b)
    have h2 : 0 < a + b := by linarith
    have h3 : b / (a + b) > 0 := by 
      apply div_pos
      exact hb
      linarith
    have h4 : a / (a + b) > 0 := by 
      apply div_pos
      exact ha
      linarith
    constructor 
    · exact h3
    constructor 
    · exact h4
    constructor 
    · -- Show that b / (a + b) + a / (a + b) = 1 
      field_simp
      <;> nlinarith 
    · -- Show that 2 * a * b / (a + b) = a * (b / (a + b)) + b * (a / (a + b))
      field_simp
      <;> ring

  have h2 : Real.sqrt (a * b) ∈ M := by
    rw [hM]
    by_cases h3 : a > b 
    · -- Assume a > b 
      have h4 : a - b > 0 := by linarith 
      have h5 : Real.sqrt (a * b) > b := by 
        nlinarith [Real.sqrt_nonneg (a * b), Real.sq_sqrt (show 0 ≤ a * b by nlinarith), sq_pos_of_pos ha, sq_pos_of_pos hb, mul_pos ha hb, sq_nonneg (a - b)]
      use (Real.sqrt (a * b) - b) / (a - b), 1 - (Real.sqrt (a * b) - b) / (a - b)
      have h6 : (Real.sqrt (a * b) - b) / (a - b) > 0 := by 
        apply div_pos 
        · -- Show that Real.sqrt (a * b) - b > 0 
          nlinarith [Real.sqrt_nonneg (a * b), Real.sq_sqrt (show 0 ≤ a * b by nlinarith), sq_pos_of_pos ha, sq_pos_of_pos hb, sq_nonneg (a - b), mul_pos ha hb]
        all_goals 
          nlinarith 
      have h7 : 1 - (Real.sqrt (a * b) - b) / (a - b) > 0 := by 
        have h8 : (Real.sqrt (a * b) - b) / (a - b) < 1 := by
          apply (div_lt_iff₀ (by linarith)).mpr 
          nlinarith [Real.sqrt_nonneg (a * b), Real.sq_sqrt (show 0 ≤ a * b by nlinarith), sq_pos_of_pos ha, sq_pos_of_pos hb, sq_nonneg (a - b), mul_pos ha hb]
        linarith 
      constructor 
      · exact h6 
      constructor 
      · exact h7 
      constructor 
      · -- Show that (Real.sqrt (a * b) - b) / (a - b) + (1 - (Real.sqrt (a * b) - b) / (a - b)) = 1 
        linarith 
      · -- Show that Real.sqrt (a * b) = a * ((Real.sqrt (a * b) - b) / (a - b)) + b * (1 - (Real.sqrt (a * b) - b) / (a - b))
        field_simp [(show a - b ≠ 0 by 
          intro h 
          apply hab 
          linarith 
        )]
        <;> nlinarith [Real.sqrt_nonneg (a * b), Real.sq_sqrt (show 0 ≤ a * b by nlinarith), sq_pos_of_pos ha, sq_pos_of_pos hb, sq_nonneg (a - b), mul_pos ha hb]
    · -- Assume a ≤ b 
      have h4 : a < b := by 
        by_contra h 
        push_neg at h 
        have : a = b := by linarith 
        contradiction 
      have h5 : b - a > 0 := by linarith 
      have h6 : Real.sqrt (a * b) < b := by 
        nlinarith [Real.sqrt_nonneg (a * b), Real.sq_sqrt (show 0 ≤ a * b by nlinarith), sq_pos_of_pos ha, sq_pos_of_pos hb, mul_pos ha hb, sq_nonneg (b - a)]
      use (Real.sqrt (a * b) - b) / (a - b), 1 - (Real.sqrt (a * b) - b) / (a - b)
      have h7 : (Real.sqrt (a * b) - b) / (a - b) > 0 := by 
        apply div_pos_of_neg_of_neg 
        · -- Show that Real.sqrt (a * b) - b < 0 
          nlinarith [Real.sqrt_nonneg (a * b), Real.sq_sqrt (show 0 ≤ a * b by nlinarith), sq_pos_of_pos ha, sq_pos_of_pos hb, sq_nonneg (a - b), mul_pos ha hb]
        all_goals 
          nlinarith 
      have h8 : 1 - (Real.sqrt (a * b) - b) / (a - b) > 0 := by 
        have h9 : (Real.sqrt (a * b) - b) / (a - b) < 1 := by 
          apply (div_lt_iff_of_neg' (by linarith)).mpr 
          nlinarith [Real.sqrt_nonneg (a * b), Real.sq_sqrt (show 0 ≤ a * b by nlinarith), sq_pos_of_pos ha, sq_pos_of_pos hb, sq_nonneg (a - b), mul_pos ha hb]
        linarith 
      constructor 
      · exact h7 
      constructor 
      · exact h8 
      constructor 
      · -- Show that (Real.sqrt (a * b) - b) / (a - b) + (1 - (Real.sqrt (a * b) - b) / (a - b)) = 1 
        linarith 
      · -- Show that Real.sqrt (a * b) = a * ((Real.sqrt (a * b) - b) / (a - b)) + b * (1 - (Real.sqrt (a * b) - b) / (a - b))
        field_simp [(show a - b ≠ 0 by 
          intro h 
          apply hab 
          linarith 
        )]
        <;> nlinarith [Real.sqrt_nonneg (a * b), Real.sq_sqrt (show 0 ≤ a * b by nlinarith), sq_pos_of_pos ha, sq_pos_of_pos hb, sq_nonneg (a - b), mul_pos ha hb]

  exact ⟨h1, h2⟩