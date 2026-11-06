import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_190075 (x : ℝ) :
  (25 : ℝ)^x < 6 * 5^x - 5 ↔ x ∈ Ioo 0 1 := by
  constructor
  · -- Forward direction: (25 : ℝ)^x < 6 * 5^x - 5 → x ∈ Ioo 0 1
    intro h
    have h1 : (25 : ℝ)^x = (5 : ℝ)^(2 * x) := by
      rw [show (25 : ℝ) = (5 : ℝ)^(2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    rw [h1] at h
    have h2 : (5 : ℝ)^(2 * x) - 6 * (5 : ℝ)^x + 5 < 0 := by linarith
    have h3 : (5 : ℝ)^(2 * x) = ((5 : ℝ)^x) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    have h4 : ((5 : ℝ)^x) ^ 2 - 6 * (5 : ℝ)^x + 5 < 0 := by
      calc
        ((5 : ℝ)^x) ^ 2 - 6 * (5 : ℝ)^x + 5 = (5 : ℝ)^(2 * x) - 6 * (5 : ℝ)^x + 5 := by
          rw [h3]
        _ < 0 := by linarith [h2]
    have h5 : ((5 : ℝ)^x - 1 : ℝ) * ((5 : ℝ)^x - 5 : ℝ) < 0 := by
      nlinarith
    have h6 : (5 : ℝ)^x > 0 := by positivity
    by_cases h7 : (5 : ℝ)^x - 1 < 0
    · -- Case 1: (5 : ℝ)^x - 1 < 0
      have h8 : (5 : ℝ)^x < (1 : ℝ) := by nlinarith
      have h9 : (5 : ℝ)^x - 5 < 0 := by nlinarith
      have h10 : ((5 : ℝ)^x - 1 : ℝ) * ((5 : ℝ)^x - 5 : ℝ) ≥ 0 := by
        nlinarith [h6, h8, h9]
      linarith
    · -- Case 2: (5 : ℝ)^x - 1 ≥ 0
      push_neg at h7 -- h7 becomes (5 : ℝ)^x - 1 ≥ 0
      have h11 : (5 : ℝ)^x ≥ (1 : ℝ) := by nlinarith
      by_cases h12 : (5 : ℝ)^x - 5 > 0
      · -- Subcase 2a: (5 : ℝ)^x - 5 > 0
        have h13 : (5 : ℝ)^x > (5 : ℝ) := by nlinarith
        have h14 : ((5 : ℝ)^x - 1 : ℝ) * ((5 : ℝ)^x - 5 : ℝ) ≥ 0 := by
          nlinarith [h6, show (5 : ℝ)^x - 1 ≥ 0 by linarith [h7], show (5 : ℝ)^x - 5 > 0 by linarith [h12]]
        linarith
      · -- Subcase 2b: (5 : ℝ)^x - 5 ≤ 0
        push_neg at h12 -- h12 becomes (5 : ℝ)^x - 5 ≤ 0
        have h15 : (5 : ℝ)^x ≤ (5 : ℝ) := by nlinarith
        have h21 : (5 : ℝ)^x - 1 ≥ (0 : ℝ) := by linarith [h7]
        have h22 : (5 : ℝ)^x - 5 ≤ (0 : ℝ) := by linarith [h12]
        -- At this point, we have factors:
        -- (5 : ℝ)^x - 1 ≥ 0
        -- (5 : ℝ)^x - 5 ≤ 0
        -- Therefore the product is ≤ 0.
        have h16 : 0 < (x : ℝ) := by
          by_contra h
          push_neg at h
          have h17 : (5 : ℝ)^x ≤ (1 : ℝ) := by
            have h18 : (5 : ℝ) ^ x ≤ (5 : ℝ) ^ (0 : ℝ) := by
              apply Real.rpow_le_rpow_of_exponent_le
              all_goals linarith
            have h19 : (5 : ℝ) ^ (0 : ℝ) = (1 : ℝ) := by
              simp
            linarith
          nlinarith [h17, h11]
        have h17 : x < (1 : ℝ) := by
          by_contra h
          push_neg at h
          have h18 : (5 : ℝ)^x ≥ (5 : ℝ) := by
            have h19 : (5 : ℝ) ^ x ≥ (5 : ℝ) ^ (1 : ℝ) := by
              apply Real.rpow_le_rpow_of_exponent_le
              all_goals linarith
            have h20 : (5 : ℝ) ^ (1 : ℝ) = (5 : ℝ) := by
              simp
            linarith
          nlinarith [h18, h15]
        simp [Ioo, h16, h17]
        all_goals linarith
        all_goals linarith
  · -- Backward direction: x ∈ Ioo 0 1 → (25 : ℝ)^x < 6 * 5^x - 5
    rintro ⟨hx1, hx2⟩ -- We have 0 < x < 1
    have h1 : (25 : ℝ)^x = (5 : ℝ)^(2 * x) := by
      rw [show (25 : ℝ) = (5 : ℝ)^(2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
      all_goals norm_num
    have h3 : (5 : ℝ)^(2 * x) = ((5 : ℝ)^x) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      ring_nf
      all_goals norm_num
      all_goals norm_num
    rw [h1, h3]
    have h6 : (5 : ℝ)^x > (1 : ℝ) := by
      have h7 : (5 : ℝ)^x > (1 : ℝ) := by
        have h8 : (5 : ℝ)^x > (5 : ℝ)^(0 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals linarith
          all_goals linarith
        have h9 : (5 : ℝ)^(0 : ℝ) = (1 : ℝ) := by
          simp
        linarith
      linarith
    have h7 : (5 : ℝ)^x < (5 : ℝ) := by
      have h8 : (5 : ℝ)^x < (5 : ℝ) := by
        have h9 : (5 : ℝ)^x < (5 : ℝ)^(1 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals linarith
        have h10 : (5 : ℝ)^(1 : ℝ) = (5 : ℝ) := by
          simp
        linarith
      linarith
    nlinarith [show (5 : ℝ)^x ≥ 0 by positivity, sq_nonneg ((5 : ℝ)^x - 1 : ℝ), sq_nonneg ((5 : ℝ)^x - 5 : ℝ)]
    all_goals norm_num
    all_goals norm_num
    all_goals norm_num
    all_goals norm_num
    all_goals norm_num
    all_goals norm_num
    all_goals norm_num
    all_goals norm_num
    all_goals norm_num
    all_goals norm_num
    all_goals norm_num
    all_goals norm_num
    all_goals norm_num