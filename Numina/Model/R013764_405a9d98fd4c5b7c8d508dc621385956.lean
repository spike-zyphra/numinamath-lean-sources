import Mathlib

open Set Real

theorem inequalities_12064 {A B : Set ℝ}
    (hA : A = {x | (1 / 2 : ℝ) ^ x ≤ 1}) (hB : B = {x | x ^ 2 - 6 * x + 8 ≤ 0}) :
    A ∩ (univ \ B) = {x | 0 ≤ x ∧ x < 2 ∨ x > 4} := by
  ext x
  simp [hA, hB]
  constructor
  · -- Assume x ∈ A ∩ (univ \ B)
    intro h
    rcases h with ⟨hA, hB⟩
    have h1 : 0 ≤ x := by
      by_contra hx
      push_neg at hx
      have h2 : (1 / 2 : ℝ) ^ x > (1 : ℝ) := by
        have h3 : (1 / 2 : ℝ) ^ x > (1 / 2 : ℝ) ^ (0 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_gt
          all_goals linarith
        have h4 : (1 / 2 : ℝ) ^ (0 : ℝ) = (1 : ℝ) := by
          norm_num
        linarith [h4]
      linarith
    have h2 : x ^ 2 - 6 * x + 8 > (0 : ℝ) := by
      linarith
    have h3 : x < (2 : ℝ) ∨ x > (4 : ℝ) := by
      by_contra h
      push_neg at h
      nlinarith [sq_nonneg (x - (2 : ℝ)), sq_nonneg (x - (4 : ℝ))]
    cases h3 with
    | inl h4 =>
      left
      constructor
      · linarith
      · linarith
    | inr h4 =>
      right
      linarith
  · -- Assume x ∈ {x | 0 ≤ x ∧ x < 2 ∨ x > 4}
    intro h
    rcases h with (h | h)
    · -- Show x ∈ A ∩ (univ \ B)
      constructor
      · -- Show x ∈ A
        -- Show (1/2)^x ≤ 1
        have h1 : (1 / 2 : ℝ) ^ x ≤ (1 : ℝ) := by
          have hA1 : (1 / 2 : ℝ) ^ x ≤ (1 / 2 : ℝ) ^ (0 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_ge
            all_goals linarith [h.1, h.2]
          have hA2 : (1 / 2 : ℝ) ^ (0 : ℝ) = (1 : ℝ) := by
            norm_num
          linarith [hA2, hA1]
        linarith
      · -- Show x ∉ B
        -- Show x^2 - 6x + 8 > 0
        have h2 : x ^ 2 - 6 * x + 8 > (0 : ℝ) := by
          nlinarith [h.1, h.2, sq_nonneg (x - (2 : ℝ)), sq_nonneg (x - (4 : ℝ))]
        linarith
    · -- Show x ∈ A ∩ (univ \ B)
      constructor
      · -- Show x ∈ A
        have h1 : (1 / 2 : ℝ) ^ x ≤ (1 : ℝ) := by
          have hA1 : (1 / 2 : ℝ) ^ x ≤ (1 / 2 : ℝ) ^ (0 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_ge
            all_goals linarith [h]
          have hA2 : (1 / 2 : ℝ) ^ (0 : ℝ) = (1 : ℝ) := by
            norm_num
          linarith [hA2, hA1]
        linarith
      · -- Show x ∉ B
        -- Show x^2 - 6 x + 8 > 0
        have h2 : x ^ 2 - 6 * x + 8 > (0 : ℝ) := by
          nlinarith [h, sq_nonneg (x - (2 : ℝ)), sq_nonneg (x - (4 : ℝ))]
        linarith