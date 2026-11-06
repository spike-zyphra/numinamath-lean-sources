import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_9210 : range (λ x => sin x - sin (abs x)) = {y | -2 ≤ y ∧ y ≤ 2} := by
  ext y
  simp only [mem_range, mem_setOf_eq]
  constructor
  · -- Assume y in range 
    rintro ⟨x, rfl⟩ 
    have h1 : -1 ≤ sin x ∧ sin x ≤ 1 := by
      constructor
      · apply Real.neg_one_le_sin 
      · apply Real.sin_le_one 
    have h2 : -1 ≤ sin (abs x) ∧ sin (abs x) ≤ 1 := by
      constructor
      · apply Real.neg_one_le_sin 
      · apply Real.sin_le_one 
    constructor
    · linarith 
    · linarith 
  · -- Assume y ∈ { y | -2 ≤ y ∧ y ≤ 2 }
    rintro ⟨hy1, hy2⟩ 
    have h3 : -1 ≤ y / 2 := by linarith 
    have h4 : y / 2 ≤ 1 := by linarith 
    have h5 : sin (arcsin (y / 2)) = y / 2 := by
      apply Real.sin_arcsin h3 h4
    by_cases h6 : y = 0 
    · -- If y = 0 
      rw [h6] 
      use 0 
      norm_num 
    · -- If y ≠ 0 
      have h7 : y ≠ 0 := by 
        intro h 
        apply h6 
        linarith 
      use (arcsin (y / 2) - 2 * π)
      have h8 : arcsin (y / 2) - 2 * π < 0 := by 
        have h11 : arcsin (y / 2) ≤ Real.pi / 2 := by 
          linarith [Real.arcsin_le_pi_div_two (y / 2), h3, h4]
        have h10 : arcsin (y / 2) < 2 * Real.pi := by 
          nlinarith [h11, Real.pi_gt_314 ]
        linarith [h10, Real.pi_gt_314 ]
      have h9 : abs (arcsin (y / 2) - 2 * π) = 2 * π - arcsin (y / 2) := by 
        rw [abs_of_neg h8]
        all_goals linarith 
      have h10 : sin (arcsin (y / 2) - 2 * π) = y / 2 := by 
        rw [sin_sub]
        simp [Real.sin_two_pi, Real.cos_two_pi, h5]
      have h13 : sin (abs (arcsin (y / 2) - 2 * π)) = - (y / 2) := by 
        rw [h9]
        have h14 : sin (2 * π - arcsin (y / 2)) = - (y / 2) := by 
          rw [sin_sub]
          simp [Real.sin_two_pi, Real.cos_two_pi, h5]
        exact h14 
      linarith [h10, h13]