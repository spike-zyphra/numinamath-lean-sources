import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_269465 (α : ℝ) (c : ℝ) (a : ℝ)
  (hα : α = π / 6) (hc : c = 50) (ha : a = 50 * sqrt 3) :
  IsLeast {d | ∃ t : ℝ, d = sqrt (2 * c^2 * t^2 * (1 - sin α) - 2 * a * c * t * cos α + a^2)} (25 * sqrt 3) := by

  have h1 : sin α = 1 / 2 := by
    rw [hα]
    have h1 : sin (π / 6) = 1 / 2 := by
      exact sin_pi_div_six
    linarith

  have h2 : cos α = Real.sqrt 3 / 2 := by
    rw [hα]
    have h2 : cos (π / 6) = Real.sqrt 3 / 2 := by
      exact cos_pi_div_six
    linarith

  constructor
  · -- First show that 25\sqrt{3} is in the set
    use (3 / 2 : ℝ)
    rw [hc, h1, h2, ha]
    have h3 : Real.sqrt (2 * (50 : ℝ) ^ 2 * (3 / 2 : ℝ) ^ 2 * (1 - (1 / 2 : ℝ)) - 2 * (50 * Real.sqrt 3) * (50 : ℝ) * (3 / 2 : ℝ) * (Real.sqrt 3 / 2) + (50 * Real.sqrt 3) ^ 2) = 25 * Real.sqrt 3 := by
      have h4 : (2 * (50 : ℝ) ^ 2 * (3 / 2 : ℝ) ^ 2 * (1 - (1 / 2 : ℝ)) - 2 * (50 * Real.sqrt 3) * (50 : ℝ) * (3 / 2 : ℝ) * (Real.sqrt 3 / 2) + (50 * Real.sqrt 3) ^ 2) = (1875 : ℝ) := by
        nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      rw [h4]
      have h5 : Real.sqrt (1875 : ℝ) = 25 * Real.sqrt 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf
        <;> norm_num
      linarith [h5]
    linarith [h3]

  · -- Show minimal
    intro d hd
    rcases hd with ⟨t, ht⟩
    have ht' : d = Real.sqrt (2 * c^2 * t^2 * (1 - sin α) - 2 * a * c * t * cos α + a^2) := ht
    have h4 : Real.sqrt (2 * c^2 * t^2 * (1 - sin α) - 2 * a * c * t * cos α + a^2) ≥ Real.sqrt (1875) := by
      apply Real.sqrt_le_sqrt
      have h5 : 2 * c^2 * t^2 * (1 - sin α) - 2 * a * c * t * cos α + a^2 ≥ 1875 := by
        rw [hc, h1, h2, ha]
        nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (t - 3 / 2)]
      linarith
    have h5 : Real.sqrt (1875 : ℝ) = 25 * Real.sqrt 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    have h6 : Real.sqrt (2 * c^2 * t^2 * (1 - sin α) - 2 * a * c * t * cos α + a^2) ≥ 25 * Real.sqrt 3 := by
      linarith [h4, h5]
    linarith [ht', h6]