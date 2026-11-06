import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_274120 (a : ℝ) :
  (∃ x : ℝ, 10^(x^2 + x) = a) ↔ a ≥ 1 / (10 ^ ((1 : ℝ) / 4)) := by
  constructor
  · -- Forward: existence implies lower bound
    rintro ⟨x, hx⟩
    have h1 : x ^ 2 + x ≥ -1 / 4 := by
      nlinarith [sq_nonneg (x + 1 / 2)]
    have h2 : (10 : ℝ) ^ (x ^ 2 + x) ≥ (10 : ℝ) ^ (-1 / 4 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · norm_num
      · linarith [h1]
    have h3 : a ≥ (10 : ℝ) ^ (-1 / 4 : ℝ) := by
      linarith [h2, hx]
    have h4 : (10 : ℝ) ^ (-1 / 4 : ℝ) = (1 / (10 : ℝ) ^ (1 / 4 : ℝ)) := by
      rw [show (10 : ℝ) ^ (-1 / 4 : ℝ) = ((10 : ℝ) ^ (1 / 4 : ℝ))⁻¹ by
        rw [← Real.rpow_neg]
        ring_nf
        all_goals norm_num
      ]
      field_simp
      all_goals norm_num
    linarith [h3, h4]
  · -- Backward: lower bound implies existence
    intro ha
    have h3 : a ≥ (10 : ℝ) ^ (-1 / 4 : ℝ) := by
      have h4 : (1 / (10 : ℝ) ^ (1 / 4 : ℝ)) = (10 : ℝ) ^ (-1 / 4 : ℝ) := by
        rw [show (10 : ℝ) ^ (-1 / 4 : ℝ) = ((10 : ℝ) ^ (1 / 4 : ℝ))⁻¹ by
          rw [← Real.rpow_neg]
          ring_nf
          all_goals norm_num
        ]
        field_simp
        all_goals norm_num
      linarith [h4, ha]
    have h4 : a > 0 := by
      have h5 : a ≥ (10 : ℝ) ^ (-1 / 4 : ℝ) := h3
      have h6 : (10 : ℝ) ^ (-1 / 4 : ℝ) > 0 := by positivity
      linarith [h5, h6]
    have h5 : ∃ r : ℝ, (10 : ℝ) ^ r = a := by
      use Real.logb 10 a
      rw [Real.rpow_logb]
      all_goals
        try linarith [h4]
        all_goals
          norm_num
      all_goals norm_num
    rcases h5 with ⟨r, hr⟩
    have h6 : r ≥ -1 / 4 := by
      by_contra h
      push_neg at h
      have h7 : (10 : ℝ) ^ r < (10 : ℝ) ^ (-1 / 4 : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_lt
        all_goals
          try linarith
          all_goals
            try nlinarith
        all_goals try nlinarith
      have h8 : (10 : ℝ) ^ (-1 / 4 : ℝ) ≤ a := by linarith [h3]
      have h9 : (10 : ℝ) ^ r = a := hr
      linarith [h7, h8, h9]
    have h7 : (0 : ℝ) ≤ 1 + 4 * r := by nlinarith [h6]
    have h8 : ∃ x : ℝ, x ^ 2 + x = r := by
      use (-1 + Real.sqrt (1 + 4 * r)) / 2
      nlinarith [Real.sqrt_nonneg (1 + 4 * r), Real.sq_sqrt (show (0 : ℝ) ≤ 1 + 4 * r by nlinarith [h7])]
    rcases h8 with ⟨x, hx⟩
    use x
    rw [hx]
    linarith [hr]