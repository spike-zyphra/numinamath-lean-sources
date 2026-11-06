import Mathlib

open Real Set
open scoped Real

theorem algebra_187568 (x : ℝ) :
  12 * sin x - 5 * cos x = 13 ↔
  ∃ k : ℤ, x - arctan (5 / 12) = π / 2 + 2 * π * k := by
  have h2 : cos (arctan (5 / 12 : ℝ)) = 12 / 13 := by
    rw [cos_arctan]
    have h3 : Real.sqrt (1 + (5 / 12 : ℝ) ^ 2) = 13 / 12 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h3]
    field_simp
    <;> ring_nf <;> norm_num
    all_goals linarith
  have h3 : sin (arctan (5 / 12 : ℝ)) = 5 / 13 := by
    rw [sin_arctan]
    have h4 : Real.sqrt (1 + (5 / 12 : ℝ) ^ 2) = 13 / 12 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h4]
    field_simp
    <;> ring_nf <;> norm_num
    all_goals linarith
  constructor
  · -- Forward direction: assuming 12 * sin x - 5 * cos x = 13 proving the existence of k.
    intro h
    have h1 : sin (x - arctan (5 / 12)) = 1 := by
      have h6 : sin (x - arctan (5 / 12)) = sin x * cos (arctan (5 / 12)) - cos x * sin (arctan (5 / 12)) := by 
        rw [sin_sub]
        all_goals ring_nf <;> norm_num
      rw [h6]
      rw [h2, h3]
      linarith [h]
    have h4 : ∃ k : ℤ, x - arctan (5 / 12) = π / 2 + 2 * π * k := by
      have h2 : sin (x - arctan (5 / 12)) = 1 := h1
      have h5 : ∃ k : ℤ, x - arctan (5 / 12) = π / 2 + 2 * π * k := by
        rw [Real.sin_eq_one_iff] at h2
        rcases h2 with ⟨k, hk⟩
        use k
        all_goals linarith [hk]
        all_goals linarith
      exact_mod_cast h5
      all_goals linarith
    simpa using h4
  · -- Backward direction: assuming existence of k, proving the equation holds.
    rintro ⟨k, hk⟩
    have h1 : sin (x - arctan (5 / 12)) = 1 := by
      have h2 : x - arctan (5 / 12) = π / 2 + 2 * π * k := by
        linarith [hk]
      have h3 : sin (x - arctan (5 / 12)) = sin (π / 2 + 2 * π * k) := by 
        rw [h2]
        all_goals ring_nf <;> norm_num
      have h4 : sin (π / 2 + 2 * π * k) = 1 := by
        have h5 : sin (π / 2 + 2 * π * k) = cos (2 * π * k) := by 
          rw [sin_add, sin_pi_div_two, cos_pi_div_two]
          all_goals ring_nf <;> norm_num
        rw [h5]
        have h6 : cos (2 * π * k) = 1 := by
          have h7 : cos (2 * π * k) = 1 := by 
            have h8 : 2 * π * k = (k : ℝ) * (2 * π) := by ring
            rw [h8]
            have h22 : cos ((k : ℝ) * (2 * π)) = 1 := by 
              have h23 : cos ((k : ℝ) * (2 * π)) = 1 := by 
                have h24 : cos ((k : ℝ) * (2 * π)) = 1 := by
                  have h25 : (k : ℝ) * (2 * π) = (k : ℤ) * (2 * π) := by
                    simp
                  rw [h25]
                  rw [cos_int_mul_two_pi]
                linarith [h24]
              linarith [h23]
            linarith [h22]
          linarith [h7]
        all_goals linarith [h6]
      all_goals linarith [h3, h4]
      all_goals linarith [h4]
    have hx_eq : 12 * sin x - 5 * cos x = 13 := by
      have h4 : sin (x - arctan (5 / 12)) = sin x * cos (arctan (5 / 12)) - cos x * sin (arctan (5 / 12)) := by 
        rw [sin_sub]
        all_goals ring_nf <;> norm_num
      have eq1 : sin (x - arctan (5 / 12)) = 1 := h1
      rw [h4] at eq1
      rw [h2, h3] at eq1
      linarith [eq1]
      all_goals linarith [eq1]
    linarith [hx_eq]