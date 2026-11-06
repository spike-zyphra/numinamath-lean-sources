import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_200671 : ∑ i ∈ Finset.range 89, sin (π * (i + 1) / 180) ^ 2 = 44.5 := by
  have h1 : ∀ i, sin (π * (i + 1) / 180) ^ 2 + sin (π * (89 - i) / 180) ^ 2 = 1 := by
    intro i
    have h2 : sin (π * (89 - i) / 180) = cos (π * (i + 1) / 180) := by
      have h3 : π * (89 - i) / 180 = π / 2 - π * (i + 1) / 180 := by 
        ring
      rw [h3]
      rw [sin_pi_div_two_sub]
    rw [h2]
    have h4 : sin (π * (i + 1) / 180) ^ 2 + cos (π * (i + 1) / 180) ^ 2 = 1 := by 
      exact Real.sin_sq_add_cos_sq (π * (i + 1) / 180)
    linarith [h4]
  have h2 : ∑ i in Finset.range 89, sin (π * (i + 1) / 180) ^ 2 = 
          (∑ i in Finset.range 44, (sin (π * (i + 1) / 180) ^ 2 + sin (π * (89 - i) / 180) ^ 2)) + 
          sin (π * (44 + 1) / 180) ^ 2 := by
    simp [Finset.sum_range_succ]
    <;> ring
  rw [h2]
  have h3 : ∑ i in Finset.range 44, (sin (π * (i + 1) / 180) ^ 2 + sin (π * (89 - i) / 180) ^ 2) = 44 := by
    simp [Finset.sum_range_succ, h1]
    <;> ring
  rw [h3]
  have h4 : sin (π * (44 + 1) / 180) ^ 2 = 0.5 := by 
    have h5 : π * (44 + 1) / 180 = π / 4 := by 
      ring
    rw [h5]
    have h6 : sin (π / 4) = Real.sqrt 2 / 2 := by 
      exact sin_pi_div_four
    rw [h6]
    have h7 : (Real.sqrt 2 / 2) ^ 2 = (1 : ℝ) / 2 := by 
      calc 
        (Real.sqrt 2 / 2) ^ 2 = (Real.sqrt 2 ^ 2) / 4 := by ring
        _ = (2) / 4 := by rw [Real.sq_sqrt]; linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
        _ = (1 : ℝ) / 2 := by ring
    rw [h7]
    norm_num
  rw [h4]
  all_goals norm_num