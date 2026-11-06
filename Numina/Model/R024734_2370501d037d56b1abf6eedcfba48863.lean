import Mathlib

open Real Set
open scoped Real

theorem algebra_278882 :
  IsGreatest {θ : ℝ | θ ∈ Ioo (-π) 0 ∧ (1 - sin θ + cos θ) / (1 - sin θ - cos θ) +
    (1 - sin θ - cos θ) / (1 - sin θ + cos θ) = 2} (-π/2) := by
  constructor
  · -- Show that -π/2 is in the set
    constructor
    · -- Show that -π/2 ∈ Ioo (-π) 0
      constructor
      · -- Show that -π < -π/2
        linarith [Real.pi_pos]
      · -- Show that -π/2 < 0
        linarith [Real.pi_pos]
    · -- Show that the equation holds at θ = -π/2
      have h1 : sin (-π / 2) = -1 := by
        have h2 : sin (-π / 2) = -sin (π / 2) := by
          have h3 : sin (-π / 2) = sin (-(π / 2)) := by ring
          rw [h3]
          rw [sin_neg]
        rw [h2]
        rw [sin_pi_div_two]
      have h2 : cos (-π / 2) = 0 := by
        have h3 : cos (-π / 2) = 0 := by
          have h4 : cos (-π / 2) = cos (-(π / 2)) := by ring
          rw [h4]
          rw [cos_neg]
          rw [cos_pi_div_two]
        exact h3
      rw [h1, h2]
      norm_num
  · -- Show that -π/2 is greatest in the set
    intro θ h
    rcases h with ⟨h1, h2⟩
    rcases h1 with ⟨h3, h4⟩
    have h5 : (1 - sin θ + cos θ) / (1 - sin θ - cos θ) + (1 - sin θ - cos θ) / (1 - sin θ + cos θ) = 2 := h2
    by_cases h6 : 1 - sin θ - cos θ = 0
    · -- If 1 - sin θ - cos θ = 0, then the original equation has division by zero.
      have h7 : 1 - sin θ - cos θ = 0 := h6
      have h8 : (1 - sin θ + cos θ) / (1 - sin θ - cos θ) + (1 - sin θ - cos θ) / (1 - sin θ + cos θ) = 0 := by
        rw [h7]
        norm_num [h7]
      rw [h8] at h5
      linarith
    · -- If 1 - sin θ + cos θ = 0, then the original equation has division by zero.
      by_cases h7 : 1 - sin θ + cos θ = 0
      · -- If 1 - sin θ + cos θ = 0, then the original equation has division by zero.
        have h8 : (1 - sin θ + cos θ) / (1 - sin θ - cos θ) + (1 - sin θ - cos θ) / (1 - sin θ + cos θ) = 0 := by
          rw [show 1 - sin θ + cos θ = 0 by linarith]
          norm_num [h7]
        rw [h8] at h5
        linarith
      · -- If neither denominator is zero, then we can manipulate the equation.
        have h8 : (1 - sin θ + cos θ) / (1 - sin θ - cos θ) + (1 - sin θ - cos θ) / (1 - sin θ + cos θ) = 2 := h5
        have h10 : (1 - sin θ + cos θ) ^ 2 + (1 - sin θ - cos θ) ^ 2 = 2 * ((1 - sin θ - cos θ) * (1 - sin θ + cos θ)) := by
          have h11 : (1 - sin θ - cos θ) ≠ 0 := by
            intro h
            apply h6
            all_goals linarith
          have h12 : (1 - sin θ + cos θ) ≠ 0 := by
            intro h
            apply h7
            all_goals linarith
          field_simp [h11, h12] at h8 ⊢
          nlinarith [sq_nonneg ((1 - sin θ + cos θ) - (1 - sin θ - cos θ)), sq_nonneg ( (1 - sin θ - cos θ) ), sq_nonneg ( (1 - sin θ + cos θ) ) ]
        have h70 : cos θ ^ 2 = 0 := by
          nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (sin θ), sq_nonneg (cos θ), sq_nonneg (sin θ ^ 2), sq_nonneg (cos θ ^ 2)]
        have h71 : cos θ = 0 := by
          nlinarith [sq_nonneg (cos θ)]
        have h72 : θ ≤ -π / 2 := by
          by_contra h
          push_neg at h
          have h73 : cos θ > 0 := by
            apply cos_pos_of_mem_Ioo
            constructor
            · -- Show that -π/2 < θ
              nlinarith
            · -- Show that θ < π/2
              nlinarith [Real.pi_pos, h4]
          nlinarith [h71, h73]
        linarith