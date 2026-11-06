import Mathlib


open Real Set


theorem algebra_187303 (x : ℝ) :
    8 * Real.sin x - 6 * Real.cos x = 10 ↔
    ∃ k : ℤ, x = Real.arctan (3 / 4) + Real.pi / 2 + 2 * Real.pi * k := by
  constructor
  · -- Forward direction: if 8 sin x - 6 cos x = 10, then x = arctan(3/4) + pi/2 + 2pi k
    intro h
    have h1 : sin (x - Real.arctan (3 / 4)) = 1 := by
      have h2 : sin (x - Real.arctan (3 / 4)) = sin x * cos (Real.arctan (3 / 4)) - cos x * sin (Real.arctan (3 / 4)) := by
        rw [sin_sub]
      have h3 : cos (Real.arctan (3 / 4)) = 4 / 5 := by
        have h4 : Real.cos (Real.arctan (3 / 4)) = 1 / Real.sqrt (1 + (3 / 4) ^ 2) := by 
          rw [Real.cos_arctan]
        have h5 : Real.sqrt (1 + (3 / 4 : ℝ) ^ 2) = 5 / 4 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h5] at h4
        field_simp at h4 ⊢
        linarith
      have h6 : sin (Real.arctan (3 / 4)) = 3 / 5 := by
        have h7 : sin (Real.arctan (3 / 4)) = (3 / 4) / Real.sqrt (1 + (3 / 4 : ℝ) ^ 2) := by
          rw [Real.sin_arctan]
        have h8 : Real.sqrt (1 + (3 / 4 : ℝ) ^ 2) = 5 / 4 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h8] at h7
        field_simp at h7 ⊢ 
        linarith
      rw [h2, h3, h6]
      nlinarith [Real.sin_sq_add_cos_sq x]
    have h2 : ∃ k : ℤ, x - Real.arctan (3 / 4) = Real.pi / 2 + 2 * Real.pi * k := by
      rw [Real.sin_eq_one_iff] at h1
      rcases h1 with ⟨k, hk⟩
      refine ⟨k, by linarith⟩
    rcases h2 with ⟨k, hk⟩
    refine ⟨k, by linarith⟩
  · -- Backward direction: if x = arctan(3/4) + pi/2 + 2pi k, then 8 sin x - 6 cos x = 10
    rintro ⟨k, hk⟩
    have h1 : sin (x - Real.arctan (3 / 4)) = 1 := by
      have h2 : x - Real.arctan (3 / 4) = Real.pi / 2 + 2 * Real.pi * (k : ℝ) := by
        linarith
      rw [h2]
      have h3 : sin (Real.pi / 2 + 2 * Real.pi * (k : ℝ) ) = 1 := by
        have h4 : sin (Real.pi / 2 + 2 * Real.pi * (k : ℝ) ) = sin (Real.pi / 2) := by
          have eq1 : Real.pi / 2 + 2 * Real.pi * (k : ℝ) = Real.pi / 2 + (k : ℝ) * (2 * Real.pi) := by ring
          rw [eq1]
          have eq2 : sin (Real.pi / 2 + (k : ℝ) * (2 * Real.pi)) = sin (Real.pi / 2) := by
            rw [Real.sin_add_int_mul_two_pi]
          linarith 
        rw [h4, Real.sin_pi_div_two]
      linarith
    have eq1 : 8 * sin x - 6 * cos x = 10 * sin (x - Real.arctan (3 / 4)) := by
      have h2 : sin (x - Real.arctan (3 / 4)) = sin x * cos (Real.arctan (3 / 4)) - cos x * sin (Real.arctan (3 / 4)) := by
        rw [sin_sub]
      have h3 : cos (Real.arctan (3 / 4)) = 4 / 5 := by
        have h4 : Real.cos (Real.arctan (3 / 4)) = 1 / Real.sqrt (1 + (3 / 4) ^ 2) := by 
          rw [Real.cos_arctan]
        have h5 : Real.sqrt (1 + (3 / 4 : ℝ) ^ 2) = 5 / 4 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h5] at h4
        field_simp at h4 ⊢
        linarith
      have h6 : sin (Real.arctan (3 / 4)) = 3 / 5 := by
        have h7 : sin (Real.arctan (3 / 4)) = (3 / 4) / Real.sqrt (1 + (3 / 4 : ℝ) ^ 2) := by
          rw [Real.sin_arctan]
        have h8 : Real.sqrt (1 + (3 / 4 : ℝ) ^ 2) = 5 / 4 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h8] at h7
        field_simp at h7 ⊢ 
        linarith
      rw [h2, h3, h6]
      nlinarith [Real.sin_sq_add_cos_sq x]
    rw [h1] at eq1
    linarith