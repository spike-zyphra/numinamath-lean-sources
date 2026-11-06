import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_120553 {a : ℝ} (ha : a ≠ 0) (M : Set ℝ)
  (hM : M = {x | (a * x - 5) / (x ^ 2 - a) < 0}) :
  3 ∈ M ∧ ¬5 ∈ M → (1 ≤ a ∧ a < 5 / 3 ∨ 9 < a ∧ a ≤ 25) := by 
  intro h 
  rcases h with ⟨h3, h5⟩ 
  have h3' : (a * 3 - 5) / (3 ^ 2 - a) < 0 := by 
    rw [hM] at h3 
    exact h3 
  have h5' : ¬ ((a * 5 - 5) / (5 ^ 2 - a) < 0) := by 
    rw [hM] at h5 
    exact h5 
  by_cases h1 : 3 ^ 2 - a = 0 
  · -- 3^2 - a = 0, so a = 9.
    have ha_eq_9 : a = 9 := by 
      linarith 
    rw [ha_eq_9] at h3' 
    norm_num [ha_eq_9] at h3' 
  · -- Assume denominator is not zero.
    have h2a : (a * 3 - 5) * (3 ^ 2 - a) < 0 := by 
      by_cases h3a : 3 ^ 2 - a > 0 
      · -- Denominator is positive.
        have h3b : a * 3 - 5 < 0 := by 
          by_contra h 
          push_neg at h 
          have h6 : (a * 3 - 5) / (3 ^ 2 - a) ≥ 0 := by 
            apply div_nonneg 
            nlinarith 
            linarith 
          linarith 
        have : (a * 3 - 5) * (3 ^ 2 - a) < 0 := by 
          apply mul_neg_of_neg_of_pos 
          linarith 
          linarith 
        linarith 
      · -- Denominator is not positive, so it's negative or zero.
        by_cases h3b : 3 ^ 2 - a < 0 
        · -- Denominator is negative.
          have h3c : a * 3 - 5 > 0 := by 
            by_contra h 
            push_neg at h 
            have h6 : (a * 3 - 5) / (3 ^ 2 - a) ≥ 0 := by 
              apply div_nonneg_of_nonpos 
              nlinarith 
              linarith 
            linarith 
          have : (a * 3 - 5) * (3 ^ 2 - a) < 0 := by 
            apply mul_neg_of_pos_of_neg 
            linarith 
            linarith 
          linarith 
        · -- Denominator is zero.
          have : 3 ^ 2 - a = 0 := by linarith 
          contradiction 
    by_cases h5a : 5 ^ 2 - a = 0 
    · -- Denominator is zero, so a = 25.
      have ha_eq_25 : a = 25 := by 
        linarith 
      right 
      constructor 
      · -- 9 < a 
        linarith 
      · -- a ≤ 25 
        linarith 
    · -- Assume denominator is not zero.
      by_cases h5d : 5 ^ 2 - a > 0 
      · -- Denominator is positive a < 25
        have h5e : a * 5 - 5 ≥ 0 := by 
          by_contra h 
          push_neg at h 
          have h6 : (a * 5 - 5) / (5 ^ 2 - a) < 0 := by 
            apply div_neg_of_neg_of_pos 
            linarith 
            linarith 
          linarith 
        have h5h : a ≥ 1 := by linarith 
        by_cases h5k : a > 9 
        · -- If a > 9, then 9 < a ∧ a ≤ 25
          right 
          constructor <;> linarith 
        · -- a ≤ 9 
          have ha5 : a < 5 / 3 := by 
            nlinarith 
          left 
          constructor 
          · -- 1 ≤ a 
            linarith 
          · -- a < 5 / 3 
            linarith 
      · -- Denominator is not positive, so it's negative or zero.
        have h5a'_ne_zero : 5 ^ 2 - a ≠ 0 := by 
          intro h 
          apply h5a 
          all_goals linarith 
        have h5d' : 5 ^ 2 - a < 0 := by 
          by_contra h 
          push_neg at h 
          have : 5 ^ 2 - a = 0 := by linarith 
          contradiction 
        -- Denominator is negative: a > 25
        exfalso
        -- contradiction for h5' with a > 25
        have h5e : a * 5 - 5 ≤ 0 := by
          by_contra h 
          push_neg at h 
          have h6 : (a * 5 - 5) / (5 ^ 2 - a) < 0 := by 
            apply div_neg_of_pos_of_neg 
            linarith 
            linarith 
          -- h5' says ¬ h6
          tauto 
        nlinarith