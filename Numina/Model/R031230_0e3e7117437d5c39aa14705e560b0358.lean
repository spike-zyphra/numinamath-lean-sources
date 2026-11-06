import Mathlib

open BigOperators Real Set

theorem inequalities_603971 (f : ℝ → ℝ) (a b c : ℝ)
    (h₀ : ∀ x, f x = 2 ^ x / (2 ^ x + 1)) (h₁ : a ≤ b) (h₂ : b ≤ c) :
    f (a - b) + f (b - c) + f (c - a) ≤ 3 / 2 := by

  have h30 : f (a - b) + f (b - c) + f (c - a) = 2 - (f (b - a) + f (c - b) - f (c - a)) := by
    have h4 : f (a - b) = 1 - f (b - a) := by
      have h5 : f (a - b) + f (b - a) = 1 := by
        rw [h₀ (a - b), h₀ (b - a)]
        have h7 : (2 : ℝ) ^ (a - b) / ((2 : ℝ) ^ (a - b) + 1) + (2 : ℝ) ^ (b - a) / ((2 : ℝ) ^ (b - a) + 1) = 1 := by
          have h8 : (2 : ℝ) ^ (b - a) = 1 / (2 : ℝ) ^ (a - b) := by
            rw [show b - a = -(a - b) by ring]
            rw [Real.rpow_neg]
            all_goals norm_num
          rw [h8]
          field_simp
          <;> nlinarith
        linarith
      linarith
    have h5 : f (b - c) = 1 - f (c - b) := by
      have h6 : f (b - c) + f (c - b) = 1 := by
        rw [h₀ (b - c), h₀ (c - b)]
        have h7 : (2 : ℝ) ^ (b - c) / ((2 : ℝ) ^ (b - c) + 1) + (2 : ℝ) ^ (c - b) / ((2 : ℝ) ^ (c - b) + 1) = 1 := by
          have h8 : (2 : ℝ) ^ (c - b) = 1 / (2 : ℝ) ^ (b - c) := by
            rw [show c - b = -(b - c) by ring]
            rw [Real.rpow_neg]
            all_goals norm_num
          rw [h8]
          field_simp
          <;> nlinarith
        linarith
      linarith
    linarith

  have h90 : f (b - a) + f (c - b) - f (c - a) ≥ 1 / 2 := by
    have h12 : f (b - a) = (2 ^ (b - a) / (2 ^ (b - a) + 1)) := by
      rw [h₀]
    have h13 : f (c - b) = (2 ^ (c - b) / (2 ^ (c - b) + 1)) := by
      rw [h₀]
    have h14 : f (c - a) = (2 ^ (c - a) / (2 ^ (c - a) + 1)) := by
      rw [h₀]
    rw [h12, h13, h14]
    have h15 : (2 : ℝ) ^ (c - a) = (2 : ℝ) ^ (b - a) * (2 : ℝ) ^ (c - b) := by
      have h16 : c - a = (b - a) + (c - b) := by linarith
      rw [h16]
      rw [← Real.rpow_add]
      all_goals
        linarith
    rw [h15]
    have h100 : (2 : ℝ) ^ (b - a) ≥ 1 := by
      have h101 : b - a ≥ 0 := by linarith
      have h102 : (2 : ℝ) ^ (b - a) ≥ (2 : ℝ) ^ (0 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
        all_goals
          linarith
      have h103 : (2 : ℝ) ^ (0 : ℝ) = 1 := by
        norm_num
      nlinarith
    have h104 : (2 : ℝ) ^ (c - b) ≥ 1 := by
      have h105 : c - b ≥ 0 := by linarith
      have h106 : (2 : ℝ) ^ (c - b) ≥ (2 : ℝ) ^ (0 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
        all_goals
          linarith
      have h107 : (2 : ℝ) ^ (0 : ℝ) = 1 := by
        norm_num
      nlinarith
    have h110 : (2 : ℝ) ^ (b - a) / ((2 : ℝ) ^ (b - a) + 1) + (2 : ℝ) ^ (c - b) / ((2 : ℝ) ^ (c - b) + 1) - ((2 : ℝ) ^ (b - a) * (2 : ℝ) ^ (c - b) ) / ((2 : ℝ) ^ (b - a) * (2 : ℝ) ^ (c - b) + 1) ≥ 1 / 2 := by
      have h1000 : 0 < (2 : ℝ) ^ (b - a) := by positivity
      have h1001 : 0 < (2 : ℝ) ^ (c - b) := by positivity
      have h1002 : 0 < (2 : ℝ) ^ (b - a) * (2 : ℝ) ^ (c - b) := mul_pos h1000 h1001
      have h114 : (2 : ℝ) ^ (b - a) / ((2 : ℝ) ^ (b - a) + 1) + (2 : ℝ) ^ (c - b) / ((2 : ℝ) ^ (c - b) + 1) - ((2 : ℝ) ^ (b - a) * (2 : ℝ) ^ (c - b) ) / ((2 : ℝ) ^ (b - a) * (2 : ℝ) ^ (c - b) + 1) - 1 / 2 ≥ 0 := by
        have h116 : (2 : ℝ) ^ (b - a) / ((2 : ℝ) ^ (b - a) + 1) + (2 : ℝ) ^ (c - b) / ((2 : ℝ) ^ (c - b) + 1) - ((2 : ℝ) ^ (b - a) * (2 : ℝ) ^ (c - b) ) / ((2 : ℝ) ^ (b - a) * (2 : ℝ) ^ (c - b) + 1) - 1 / 2 =
            ( 2 * ( (2 : ℝ) ^ (b - a) * ( (2 : ℝ) ^ (c - b) + 1 ) * ( (2 : ℝ) ^ (b - a) * (2 : ℝ) ^ (c - b) + 1 ) ) + 2 * ( (2 : ℝ) ^ (c - b) * ( (2 : ℝ) ^ (b - a) + 1 ) * ( (2 : ℝ) ^ (b - a) * (2 : ℝ) ^ (c - b) + 1 ) ) - 2 * ( (2 : ℝ) ^ (b - a) * (2 : ℝ) ^ (c - b) * ( (2 : ℝ) ^ (b - a) + 1 ) * ( (2 : ℝ) ^ (c - b) + 1 ) ) - ( (2 : ℝ) ^ (b - a) + 1 ) * ( (2 : ℝ) ^ (c - b) + 1 ) * ( (2 : ℝ) ^ (b - a) * (2 : ℝ) ^ (c - b) + 1 ) ) / ( 2 * ( (2 : ℝ) ^ (b - a) + 1 ) * ( (2 : ℝ) ^ (c - b) + 1 ) * ( (2 : ℝ) ^ (b - a) * (2 : ℝ) ^ (c - b) + 1 ) ) := by
          field_simp
          ring
        rw [h116]
        have h117 : 2 * ( (2 : ℝ) ^ (b - a) * ( (2 : ℝ) ^ (c - b) + 1 ) * ( (2 : ℝ) ^ (b - a) * (2 : ℝ) ^ (c - b) + 1 ) ) + 2 * ( (2 : ℝ) ^ (c - b) * ( (2 : ℝ) ^ (b - a) + 1 ) * ( (2 : ℝ) ^ (b - a) * (2 : ℝ) ^ (c - b) + 1 ) ) - 2 * ( (2 : ℝ) ^ (b - a) * (2 : ℝ) ^ (c - b) * ( (2 : ℝ) ^ (b - a) + 1 ) * ( (2 : ℝ) ^ (c - b) + 1 ) ) - ( (2 : ℝ) ^ (b - a) + 1 ) * ( (2 : ℝ) ^ (c - b) + 1 ) * ( (2 : ℝ) ^ (b - a) * (2 : ℝ) ^ (c - b) + 1 ) ≥ 0 := by
          have h10000 : (2 : ℝ) ^ (b - a) ≥ 1 := h100
          have h10001 : (2 : ℝ) ^ (c - b) ≥ 1 := h104
          nlinarith [sq_nonneg ( (2 : ℝ) ^ (b - a) - 1 ), sq_nonneg ( (2 : ℝ) ^ (c - b) - 1 ), sq_nonneg ( (2 : ℝ) ^ (b - a) * (2 : ℝ) ^ (c - b) - 1 ), mul_nonneg (show 0 ≤ (2 : ℝ) ^ (b - a) - 1 by nlinarith) (show 0 ≤ (2 : ℝ) ^ (c - b) - 1 by nlinarith), mul_nonneg (show 0 ≤ (2 : ℝ) ^ (b - a) by positivity) (show 0 ≤ (2 : ℝ) ^ (c - b) by positivity), mul_nonneg (show 0 ≤ (2 : ℝ) ^ (b - a) by positivity) (show 0 ≤ (2 : ℝ) ^ (c - b) - 1 by nlinarith), mul_nonneg (show 0 ≤ (2 : ℝ) ^ (c - b) by positivity) (show 0 ≤ (2 : ℝ) ^ (b - a) - 1 by nlinarith) ]
        have h1180 : ( 2 * ( (2 : ℝ) ^ (b - a) + 1 ) * ( (2 : ℝ) ^ (c - b) + 1 ) * ( (2 : ℝ) ^ (b - a) * (2 : ℝ) ^ (c - b) + 1 ) ) > 0 := by positivity
        apply div_nonneg
        linarith
        all_goals linarith
      linarith
    linarith

  linarith [h30, h90]