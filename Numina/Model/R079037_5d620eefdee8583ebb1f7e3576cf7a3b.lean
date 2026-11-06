import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_190239 (x : ℝ) :
  (1 / (3 ^ x + 5) : ℝ) < (1 / (3 ^ (x + 1) - 1)) ↔ x ∈ Ioo (-1) 1 := by
  constructor
  · -- Assume (1 / (3 ^ x + 5) : ℝ) < (1 / (3 ^ (x + 1) - 1)), show x ∈ Ioo (-1) 1
    intro h
    have h1 : (3 : ℝ) ^ x + 5 > 0 := by
      have h3_pos : (3 : ℝ) ^ x > 0 := by positivity
      linarith
    by_cases h2 : (3 : ℝ) ^ (x + 1) - 1 > 0
    · -- $3^{x+1} - 1 > 0$, so cross multiply directly.
      have h3 : (3 ^ (x + 1) - 1 : ℝ) > 0 := h2
      have h4 : (1 / (3 ^ x + 5) : ℝ) < (1 / (3 ^ (x + 1) - 1)) := h
      apply (one_div_lt_one_div (by linarith) (by linarith)).mp at h4
      have h5 : (3 : ℝ) ^ (x + 1) < (3 : ℝ) ^ x + 6 := by linarith
      have h6 : (3 : ℝ) ^ x < 3 := by
        have h8 : (3 : ℝ) ^ (x + 1) = (3 : ℝ) ^ x * (3 : ℝ) := by
          rw [Real.rpow_add]
          ring_nf
          all_goals linarith
        rw [h8] at h5
        nlinarith
      have h7 : x < (1 : ℝ) := by
        by_contra h7
        push_neg at h7
        have h8 : (3 : ℝ) ^ x ≥ (3 : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le
          all_goals linarith
          all_goals linarith
        have h9 : (3 : ℝ) ^ (1 : ℝ) = (3 : ℝ) := by
          simp
        have h10 : (3 : ℝ) ^ x ≥ (3 : ℝ) := by linarith [h8, h9]
        linarith [h6, h10]
      have h11 : x > (-1 : ℝ) := by
        by_contra h11
        push_neg at h11
        have h12 : x + 1 ≤ (0 : ℝ) := by linarith
        have h13 : (3 : ℝ) ^ (x + 1) ≤ (3 : ℝ) ^ (0 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le
          all_goals linarith
        have h14 : (3 : ℝ) ^ (0 : ℝ) = 1 := by
          simp
        have h15 : (3 : ℝ) ^ (x + 1) ≤ 1 := by linarith [h13, h14]
        nlinarith
      exact ⟨h11, h7⟩
    · -- $3^{x+1} - 1 \leq 0$
      have h3 : (3 ^ (x + 1) - 1 : ℝ) ≤ 0 := by
        linarith
      have h4 : (1 / (3 ^ (x + 1) - 1) : ℝ) ≤ 0 := by
        apply div_nonpos_of_nonneg_of_nonpos
        · norm_num
        · linarith [h3]
      have h5 : (1 / (3 ^ x + 5) : ℝ) > 0 := by
        apply div_pos
        norm_num
        linarith [show (3 : ℝ) ^ x > 0 by positivity]
      linarith [h, h4, h5]
  · -- Assume x ∈ Ioo (-1) 1, show (1 / (3 ^ x + 5) : ℝ) < (1 / (3 ^ (x + 1) - 1))
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 : (3 : ℝ) ^ x + 5 > 0 := by
      have h3_pos : (3 : ℝ) ^ x > 0 := by positivity
      linarith
    have h4 : (3 : ℝ) ^ (x + 1) - 1 > 0 := by
      have h5 : (3 : ℝ) ^ (x + 1) > (3 : ℝ) ^ (0 : ℝ) := by
        have h6 : (x + 1 : ℝ) > (0 : ℝ) := by linarith
        have h7 : (3 : ℝ) ^ (0 : ℝ) = 1 := by
          simp
        have h8 : (3 : ℝ) ^ (x + 1) > (3 : ℝ) ^ (0 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals linarith
        have h9 : (3 : ℝ) ^ (0 : ℝ) = 1 := by
          simp
        linarith [h8, h9]
      have h9 : (3 : ℝ) ^ (0 : ℝ) = 1 := by
        simp
      nlinarith
    have h13 : (3 : ℝ) ^ (x + 1) - 1 < (3 : ℝ) ^ x + 5 := by
      have h10 : (3 : ℝ) ^ x < (3 : ℝ) := by
        have h11 : (3 : ℝ) ^ x < (3 : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals linarith
        have h12 : (3 : ℝ) ^ (1 : ℝ) = (3 : ℝ) := by
          simp
        linarith [h11, h12]
      have h14 : (3 : ℝ) ^ (x + 1) = (3 : ℝ) ^ x * (3 : ℝ) := by
        rw [Real.rpow_add]
        ring_nf
        all_goals linarith
      rw [h14]
      nlinarith [h10]
    have h5 : (1 / (3 ^ x + 5) : ℝ) < (1 / (3 ^ (x + 1) - 1)) := by
      apply (one_div_lt_one_div (by linarith) (by linarith)).mpr
      all_goals linarith [h13]
    exact h5