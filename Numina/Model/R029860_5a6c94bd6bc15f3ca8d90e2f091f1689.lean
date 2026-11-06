import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_313210 {f : ℝ → ℝ} (hf : f = λ x => x ^ 2 / (x - 1)) :
    StrictMonoOn f {x | x ≤ 0 ∨ x ≥ 2} := by
  intro x hx y hy hxy
  have h1 : x ≤ 0 ∨ x ≥ 2 := by 
    simpa using hx
  have h2 : y ≤ 0 ∨ y ≥ 2 := by 
    simpa using hy
  rcases h1 with (h1 | h1)
  · -- Case x ≤ 0
    rcases h2 with (h2 | h2)
    · -- Case y ≤ 0
      rw [hf]
      have h3 : x < y := hxy
      have h4 : x - 1 < 0 := by 
        nlinarith 
      have h5 : y - 1 < 0 := by 
        nlinarith 
      have h6 : (y ^ 2 / (y - 1) : ℝ) - (x ^ 2 / (x - 1) : ℝ) > 0 := by 
        have h7 : (y ^ 2 / (y - 1) : ℝ) - (x ^ 2 / (x - 1) : ℝ) = (y ^ 2 * (x - 1) - x ^ 2 * (y - 1)) / ((y - 1) * (x - 1)) := by 
          field_simp [(show (y - 1 : ℝ) ≠ 0 by 
            by_contra h 
            have : y = 1 := by linarith 
            linarith 
          ), (show (x - 1 : ℝ) ≠ 0 by 
            by_contra h 
            have : x = 1 := by linarith 
            nlinarith 
          )]
          <;> ring 
        rw [h7] at *
        apply div_pos 
        · -- Show the numerator is positive 
          have h8 : y ^ 2 * (x - 1) - x ^ 2 * (y - 1) > 0 := by 
            have h9 : y - x > 0 := by linarith 
            have h10 : x * y - x - y > 0 := by 
              nlinarith [sq_nonneg (x - 0), sq_nonneg (y - 0), show x ≤ 0 by linarith, show y ≤ 0 by linarith]
            nlinarith [show 0 ≤ x * y by nlinarith] 
          linarith 
        · -- Show the denominator is positive 
          have h9 : (y - 1 : ℝ) * (x - 1) > 0 := by 
            apply mul_pos_of_neg_of_neg 
            all_goals 
            linarith 
          linarith 
      linarith 
    · -- Case y ≥ 2
      rw [hf]
      have h7 : x - 1 < 0 := by 
        nlinarith 
      have h8 : y - 1 > 0 := by 
        nlinarith 
      have h6 : (y ^ 2 / (y - 1) : ℝ) - (x ^ 2 / (x - 1) : ℝ) > 0 := by 
        have h7 : (y ^ 2 / (y - 1) : ℝ) - (x ^ 2 / (x - 1) : ℝ) = (y ^ 2 * (x - 1) - x ^ 2 * (y - 1)) / ((y - 1) * (x - 1)) := by 
          field_simp [(show (y - 1 : ℝ) ≠ 0 by 
            by_contra h 
            have : y = 1 := by linarith 
            linarith 
          ), (show (x - 1 : ℝ) ≠ 0 by 
            by_contra h 
            have : x = 1 := by linarith 
            linarith 
          )]
          <;> ring 
        rw [h7] at *
        have h8 : y ^ 2 * (x - 1) - x ^ 2 * (y - 1) < 0 := by 
          nlinarith [show x ≤ 0 by linarith, show y ≥ 2 by linarith] 
        have h9 : (y - 1 : ℝ) * (x - 1) < 0 := by 
          apply mul_neg_of_pos_of_neg 
          all_goals 
          linarith 
        apply div_pos_of_neg_of_neg 
        all_goals 
        nlinarith 
      linarith 
  · -- Case x ≥ 2
    rcases h2 with (h2 | h2)
    · -- Case y ≤ 0
      exfalso 
      linarith 
    · -- Case y ≥ 2
      rw [hf]
      have h3 : x < y := hxy
      have h4 : x - 1 > 0 := by 
        nlinarith 
      have h5 : y - 1 > 0 := by 
        nlinarith 
      have h6 : (y ^ 2 / (y - 1) : ℝ) - (x ^ 2 / (x - 1) : ℝ) > 0 := by 
        have h7 : (y ^ 2 / (y - 1) : ℝ) - (x ^ 2 / (x - 1) : ℝ) = (y ^ 2 * (x - 1) - x ^ 2 * (y - 1)) / ((y - 1) * (x - 1)) := by 
          field_simp [(show (y - 1 : ℝ) ≠ 0 by 
            by_contra h 
            have : y = 1 := by linarith 
            linarith 
          ), (show (x - 1 : ℝ) ≠ 0 by 
            by_contra h 
            have : x = 1 := by linarith 
            linarith 
          )]
          <;> ring 
        rw [h7] at *
        apply div_pos 
        · -- Show the numerator is positive 
          have h8 : y ^ 2 * (x - 1) - x ^ 2 * (y - 1) > 0 := by 
            have h9 : y - x > 0 := by linarith 
            have h10 : x * y - x - y > 0 := by 
              nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), show x ≥ 2 by linarith, show y ≥ 2 by linarith]
            nlinarith [show x * y > 0 by nlinarith] 
          linarith 
        · -- Show the denominator is positive 
          have h9 : (y - 1 : ℝ) * (x - 1) > 0 := by 
            apply mul_pos 
            all_goals 
            linarith 
          linarith 
      linarith