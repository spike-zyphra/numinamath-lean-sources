import Mathlib

open Real

theorem inequalities_272096 :
    {x : ℝ | x ≠ -1 ∧ (x^2 - 1) / (x^2 + 1) < (x^3 - 1) / (x^3 + 1)} =
    {x : ℝ | x < -1 ∨ x > 1} := by
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor 
  · -- Assume x ≠ -1 ∧ (x^2 - 1) / (x^2 + 1) < (x^3 - 1) / (x^3 + 1)
    intro h 
    rcases h with ⟨hx1, hineq⟩ 
    by_cases h1 : x < -1 
    · -- x < -1 
      left 
      exact h1 
    · -- x ≥ -1 
      have h2 : x > -1 := by 
        by_contra h 
        push_neg at h 
        have h3 : x = -1 := by 
          have h4 : x ≤ -1 := by linarith 
          have h5 : x ≥ -1 := by linarith 
          have h6 : x = -1 := by linarith 
          exact h6 
        contradiction 
      have h3 : x > 1 := by 
        by_contra h 
        push_neg at h 
        have h4 : x ≤ 1 := by linarith 
        have h5 : x^3 + 1 > 0 := by 
          nlinarith [sq_nonneg (x + 1), sq_nonneg (x ^ 2), sq_nonneg (x - 1)]
        have h6 : (x^2 - 1) / (x^2 + 1) ≥ (x^3 - 1) / (x^3 + 1) := by 
          apply (div_le_div_iff (by positivity) (by positivity)).mpr 
          nlinarith [sq_nonneg (x^2 - 1), sq_nonneg (x^3 - 1), sq_nonneg ((x ^2 - x)), sq_nonneg ((x + 1)), sq_nonneg ((x - 1)), mul_nonneg (sq_nonneg (x ^ 2 - 1)) (sq_nonneg (x - 1))]
        linarith 
      right 
      linarith 
  · -- Assume x < -1 ∨ x > 1 
    intro h 
    rcases h with (h1 | h2)
    · -- x < -1 
      constructor 
      · -- x ≠ -1 
        by_contra h 
        have : x = -1 := by linarith 
        linarith 
      · -- prove the inequality 
        have h11 : x < -1 := h1 
        have h2 : x^3 + 1 < 0 := by 
          nlinarith [sq_nonneg (x + 1), sq_nonneg (x ^ 2), sq_nonneg (x - 1)]
        have h13 : (x^2 - 1) / (x^2 + 1) < (x^3 - 1) / (x^3 + 1) := by 
          have h5 : (x^2 - 1) / (x^2 + 1) - (x^3 - 1) / (x^3 + 1) < 0 := by 
            have h5 : (x^2 - 1) / (x^2 + 1) - (x^3 - 1) / (x^3 + 1) = (2 * x^2 * (1 - x)) / ((x^2 + 1) * (x^3 + 1)) := by 
              field_simp [(show x^2 + 1 ≠ 0 by nlinarith), (show x^3 + 1 ≠ 0 by 
                intro h3; 
                have : x = -1 := by nlinarith [sq_nonneg (x + 1)]
                linarith 
              )]
              <;> ring 
            rw [h5] 
            apply div_neg_of_pos_of_neg 
            · -- Show 2 * x^2 * (1 - x) > 0 
              nlinarith [sq_nonneg (x - 0), sq_nonneg ((x + 1) * (x - 0)), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^3 - 1)]
            · -- Show (x^2 + 1) * (x^3 + 1) < 0 
              have h7 : x^2 + 1 > 0 := by nlinarith 
              have h8 : x^3 + 1 < 0 := by nlinarith [sq_nonneg (x + 1), sq_nonneg (x ^ 2), sq_nonneg (x - 1)]
              nlinarith 
          linarith 
        exact h13 
    · -- x > 1 
      constructor 
      · -- x ≠ -1 
        by_contra h 
        have : x = -1 := by linarith 
        nlinarith 
      · -- prove the inequality 
        have h2 : x > 1 := h2 
        have h21 : x^3 + 1 > 0 := by 
          nlinarith [sq_nonneg (x + 1), sq_nonneg (x ^ 2), sq_nonneg (x - 1)]
        have h13 : (x^2 - 1) / (x^2 + 1) < (x^3 - 1) / (x^3 + 1) := by 
          have h5 : (x^2 - 1) / (x^2 + 1) - (x^3 - 1) / (x^3 + 1) < 0 := by 
            have h5 : (x^2 - 1) / (x^2 + 1) - (x^3 - 1) / (x^3 + 1) = (2 * x^2 * (1 - x)) / ((x^2 + 1) * (x^3 + 1)) := by 
              field_simp [(show x^2 + 1 ≠ 0 by nlinarith), (show x^3 + 1 ≠ 0 by 
                intro h3; 
                have : x = -1 := by nlinarith [sq_nonneg (x + 1)]
                linarith 
              )]
              <;> ring 
            rw [h5] 
            apply div_neg_of_neg_of_pos 
            · -- Show 2 * x^2 * (1 - x) < 0 
              nlinarith [sq_nonneg (x - 0), sq_nonneg ((x + 1) * (x - 0)), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^3 - 1)]
            · -- Show (x^2 + 1) * (x^3 + 1) > 0 
              have h7 : x^2 + 1 > 0 := by nlinarith 
              have h8 : x^3 + 1 > 0 := by nlinarith [sq_nonneg (x + 1), sq_nonneg (x ^ 2), sq_nonneg (x - 1)]
              nlinarith 
          linarith 
        exact h13