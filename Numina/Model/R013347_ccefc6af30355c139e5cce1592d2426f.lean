import Mathlib

open BigOperators Real Set

theorem algebra_327115 {a : ℝ} (ha : a ≠ 5) :
    (∃ x : ℝ, x < 0 ∧ (3/2)^x = (2 + 3*a)/(5-a)) ↔
    (-2/3 < a ∧ a < 3/4) := by
  constructor
  · -- Assume there exists a negative root, prove -2/3 < a < 3/4
    intro h
    rcases h with ⟨x, hx1, h_eq⟩
    have h1 : (3 / 2 : ℝ) ^ x > 0 := by positivity
    have h2 : (3 / 2 : ℝ) ^ x < 1 := by
      have h3 : (3 / 2 : ℝ) ^ (0 : ℝ) = 1 := by
        norm_num
      have h4 : (3 / 2 : ℝ) ^ x < (3 / 2 : ℝ) ^ (0 : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_lt
        all_goals
          try linarith
          try norm_num
      rw [h3] at h4
      linarith
    have h3 : 0 < (2 + 3 * a) / (5 - a) := by
      have h4 : (3 / 2 : ℝ) ^ x = (2 + 3 * a) / (5 - a) := by linarith [h_eq]
      have h5 : (2 + 3 * a) / (5 - a) > 0 := by nlinarith [h4, h1]
      linarith
    have h4 : (2 + 3 * a) / (5 - a) < 1 := by
      have h5 : (3 / 2 : ℝ) ^ x = (2 + 3 * a) / (5 - a) := by linarith [h_eq]
      have h8 : (3 / 2 : ℝ) ^ x < 1 := h2
      have h9 : (2 + 3 * a) / (5 - a) < 1 := by nlinarith [h5, h2]
      linarith
    have h5 : -2 / 3 < a := by
      by_contra h
      push_neg at h
      -- We need to show that $a \leq -2/3$ contradicts h3.
      -- If $a \leq -2/3$, then $2 + 3a \leq 0$.
      have h6 : (2 + 3 * a) ≤ 0 := by nlinarith
      -- By case analysis on the sign of the denominator.
      by_cases h7 : (5 - a) > 0
      · -- If 5 - a > 0, then the numerator must be positive.
        have h8 : (2 + 3 * a) / (5 - a) ≤ 0 := by
          apply div_nonpos_of_nonpos_of_nonneg
          · linarith
          · linarith
        linarith
      · -- If 5 - a ≤ 0, need to analyze further.
        have h77 : (5 - a) ≤ 0 := by nlinarith
        have h88 : a ≥ 5 := by nlinarith
        -- Here the numerator is ≤ 0 and denominator is ≤ 0.
        -- Therefore, the total fraction is ≥ 0.
        -- This contradicts with h3.
        have h33 : (2 + 3 * a) / (5 - a) ≤ 0 := by
          apply div_nonpos_of_nonpos_of_nonneg
          · -- Show numerator ≤ 0
            linarith
          · -- Show denominator ≥ 0
            linarith
        linarith
    have h6 : a < 3 / 4 := by
      by_contra h
      push_neg at h
      -- Now, need to show this contradicts h4.
      -- When a ≥ 3/4.
      -- When a ≥ 3/4, and 5 - a > 0, then 2 + 3a ≥ 5 - a.
      by_cases h77 : (5 - a) > 0
      · -- If 5 - a > 0
        -- Given (2 + 3a) / (5 - a) ≥ 1.
        have h8 : (2 + 3 * a) / (5 - a) ≥ 1 := by
          have h9 : 2 + 3 * a ≥ 5 - a := by
            nlinarith
          have h10 : (2 + 3 * a) / (5 - a) ≥ 1 := by
            apply (le_div_iff₀ (by linarith)).mpr
            nlinarith
          linarith
        linarith
      · -- If 5 - a ≤ 0
        have h777 : (5 - a) ≤ 0 := by nlinarith
        have h888 : a ≥ 5 := by nlinarith
        -- The numerator is positive.
        have h333 : (2 + 3 * a) / (5 - a) ≤ 0 := by
          apply div_nonpos_of_nonneg_of_nonpos
          · -- Show numerator ≥ 0
            nlinarith
          · -- Show denominator ≤ 0
            nlinarith
        linarith
    constructor
    · linarith
    · linarith
  · -- Assume -2/3 < a < 3/4, prove there exists a negative root
    rintro ⟨ha1, ha2⟩
    have h3 : (2 + 3 * a) / (5 - a) > 0 := by
      have h33 : 2 + 3 * a > 0 := by nlinarith
      have h44 : 5 - a > 0 := by nlinarith
      positivity
    have h4 : (2 + 3 * a) / (5 - a) < 1 := by
      have h55 : 2 + 3 * a < 5 - a := by
        nlinarith
      have h66 : (2 + 3 * a) / (5 - a) < 1 := by
        have h77 : 0 < (5 - a : ℝ) := by nlinarith
        apply (div_lt_iff (by linarith)).mpr
        nlinarith
      linarith
    use Real.logb (3 / 2) ((2 + 3 * a) / (5 - a))
    constructor
    · -- Show that x < 0
      have h5 : Real.logb (3 / 2) ((2 + 3 * a) / (5 - a)) < 0 := by
        have h6 : Real.logb (3 / 2) ((2 + 3 * a) / (5 - a)) < Real.logb (3 / 2) (1 : ℝ) := by
          apply Real.logb_lt_logb
          all_goals
            try linarith
            try nlinarith
        have h777 : Real.logb (3 / 2) (1 : ℝ) = 0 := by
          norm_num [Real.logb_one]
        linarith
      linarith
    · -- Show that (3/2)^x = (2 + 3*a)/(5 - a)
      have h8 : ((3 / 2 : ℝ) : ℝ) ^ Real.logb (3 / 2) ((2 + 3 * a) / (5 - a)) = (2 + 3 * a) / (5 - a) := by
        rw [Real.rpow_logb]
        all_goals
          try positivity
          try linarith
      linarith