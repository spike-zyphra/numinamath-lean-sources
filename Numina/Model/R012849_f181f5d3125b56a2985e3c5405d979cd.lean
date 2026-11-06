import Mathlib

open Real

theorem inequalities_170839 (x : ℝ) :
    (0.008 : ℝ)^x + 5^(1 - 3 * x) + (0.04 : ℝ)^(3 / 2 * (x + 1)) < 30.04 ↔
    x > -1 / 3 := by
  constructor
  · -- Assume the inequality holds, prove x > -1/3
    intro h
    have h1 : (0.008 : ℝ) ^ x = (5 : ℝ) ^ (-3 * x) := by
      have h2 : (0.008 : ℝ) = (5 : ℝ) ^ (-3 : ℝ) := by norm_num
      rw [h2]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    have h5 : (0.04 : ℝ) ^ (3 / 2 * (x + 1)) = (5 : ℝ) ^ (-3 * x - 3) := by
      have h6 : (0.04 : ℝ) = (5 : ℝ) ^ (-2 : ℝ) := by norm_num
      rw [h6]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    have h7 : (5 : ℝ) ^ (1 - 3 * x) = 5 * ((5 : ℝ) ^ (-3 * x)) := by
      have h8 : (5 : ℝ) ^ (1 - 3 * x) = ((5 : ℝ) ^ (1 : ℝ)) * ((5 : ℝ) ^ (-3 * x : ℝ)) := by
        rw [← Real.rpow_add]
        ring_nf
        all_goals linarith
      rw [h8]
      norm_num
    have h8 : (0.008 : ℝ) ^ x + (5 : ℝ) ^ (1 - 3 * x) + (0.04 : ℝ) ^ (3 / 2 * (x + 1)) =
        (5 : ℝ) ^ (-3 * x) * (1 + (5 : ℝ) + (5 : ℝ) ^ (-3 : ℝ)) := by
      rw [h1, h5]
      rw [h7]
      have h4 : (5 : ℝ) ^ (-3 * x - 3 : ℝ) = ((5 : ℝ) ^ (-3 * x : ℝ)) * ((5 : ℝ) ^ (-3 : ℝ)) := by
        rw [← Real.rpow_add]
        ring_nf
        all_goals linarith
      rw [h4]
      ring_nf
    have h9 : (5 : ℝ) ^ (-3 : ℝ) = (1 / 125 : ℝ) := by
      norm_num
    have h3 : (0.008 : ℝ) ^ x + (5 : ℝ) ^ (1 - 3 * x) + (0.04 : ℝ) ^ (3 / 2 * (x + 1)) =
        (5 : ℝ) ^ (-3 * x) * (6.008 : ℝ) := by
      rw [h8, h9]
      norm_num
    have h4 : (5 : ℝ) ^ (-3 * x) * (6.008 : ℝ) < (30.04 : ℝ) := by
      linarith [h3, h]
    -- From here, dividing both sides by 6.008 which is positive.
    have h5 : (5 : ℝ) ^ (-3 * x) < (5 : ℝ) := by
      nlinarith
    -- Now that the function 5^(-3 * x) is less than 5. Since base 5 > 1, strictly increasing.
    -- So 5^(-3 * x) < 5^1 implies the exponent is less than 1, with equality only when x approaches from above. Since it's strictly increasing.
    have h6 : -3 * x < (1 : ℝ) := by
      by_contra h7
      push_neg at h7
      have h8 : (5 : ℝ) ^ (-3 * x) ≥ (5 : ℝ) := by
        have h9 : -3 * x ≥ (1 : ℝ) := by linarith
        have h10 : (5 : ℝ) ^ (-3 * x) ≥ (5 : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le
          · norm_num
          · linarith
        have h11 : (5 : ℝ) ^ (1 : ℝ) = (5 : ℝ) := by norm_num
        rw [h11] at h10
        linarith
      linarith
    -- -3 * x < 1, multiply both sides by (-1/3) which reverses the inequality:
    -- x > -1/3
    linarith
  · -- Assume x > -1/3, prove the inequality
    intro h
    have h1 : (0.008 : ℝ) ^ x = (5 : ℝ) ^ (-3 * x) := by
      have h2 : (0.008 : ℝ) = (5 : ℝ) ^ (-3 : ℝ) := by norm_num
      rw [h2]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    have h5 : (0.04 : ℝ) ^ (3 / 2 * (x + 1)) = (5 : ℝ) ^ (-3 * x - 3) := by
      have h6 : (0.04 : ℝ) = (5 : ℝ) ^ (-2 : ℝ) := by norm_num
      rw [h6]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    have h7 : (5 : ℝ) ^ (1 - 3 * x) = 5 * ((5 : ℝ) ^ (-3 * x)) := by
      have h8 : (5 : ℝ) ^ (1 - 3 * x) = ((5 : ℝ) ^ (1 : ℝ)) * ((5 : ℝ) ^ (-3 * x : ℝ)) := by
        rw [← Real.rpow_add]
        ring_nf
        all_goals linarith
      rw [h8]
      norm_num
    have h8 : (0.008 : ℝ) ^ x + (5 : ℝ) ^ (1 - 3 * x) + (0.04 : ℝ) ^ (3 / 2 * (x + 1)) =
        (5 : ℝ) ^ (-3 * x) * (1 + (5 : ℝ) + (5 : ℝ) ^ (-3 : ℝ)) := by
      rw [h1, h5]
      rw [h7]
      have h4 : (5 : ℝ) ^ (-3 * x - 3 : ℝ) = ((5 : ℝ) ^ (-3 * x : ℝ)) * ((5 : ℝ) ^ (-3 : ℝ)) := by
        rw [← Real.rpow_add]
        ring_nf
        all_goals linarith
      rw [h4]
      ring_nf
    have h9 : (5 : ℝ) ^ (-3 : ℝ) = (1 / 125 : ℝ) := by
      norm_num
    have h3 : (0.008 : ℝ) ^ x + (5 : ℝ) ^ (1 - 3 * x) + (0.04 : ℝ) ^ (3 / 2 * (x + 1)) =
        (5 : ℝ) ^ (-3 * x) * (6.008 : ℝ) := by
      rw [h8, h9]
      norm_num
    -- We need to show this is < 30.04
    have h7 : -3 * x < (1 : ℝ) := by
      linarith
    have h8 : (5 : ℝ) ^ (-3 * x) < (5 : ℝ) := by
      have h9 : -3 * x < (1 : ℝ) := by linarith
      have h10 : (5 : ℝ) ^ (-3 * x) < (5 : ℝ) ^ (1 : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_lt
        · norm_num
        · linarith
      have h11 : (5 : ℝ) ^ (1 : ℝ) = (5 : ℝ) := by norm_num
      rw [h11] at h10
      linarith
    have h9 : (5 : ℝ) ^ (-3 * x) * (6.008 : ℝ) < (30.04 : ℝ) := by
      nlinarith
    linarith [h3, h9]