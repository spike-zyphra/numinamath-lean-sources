import Mathlib

theorem algebra_256436 (θ : ℝ) (h : Real.tan θ ≠ 0) (h1 : (1 / Real.tan θ - 1) / (2 * 1 / Real.tan θ + 1) = 1) :
    Real.cos (2 * θ) = 3 / 5 := by
  have htan_ne_zero : Real.tan θ ≠ 0 := h
  have h5 : 2 * 1 / Real.tan θ + 1 ≠ 0 := by
    by_contra h55
    have : (1 / Real.tan θ - 1) / (2 * 1 / Real.tan θ + 1) = 0 := by
      rw [h55]
      norm_num
      all_goals linarith
    linarith [h1, this]
  have htan2_simp : (1 - Real.tan θ) / (2 + Real.tan θ) = 1 := by
    have htan_ne_zero : Real.tan θ ≠ 0 := h
    have htan2_simp : (1 - Real.tan θ) / (2 + Real.tan θ) = 1 := by
      have h55 : 2 * 1 / Real.tan θ + 1 ≠ 0 := h5
      have h11 : (1 / Real.tan θ - 1) / (2 * 1 / Real.tan θ + 1) = 1 := h1
      have : (1 / Real.tan θ - 1) / (2 * 1 / Real.tan θ + 1) = (1 - Real.tan θ) / (2 + Real.tan θ) := by
        have htan_ne_zero : Real.tan θ ≠ 0 := h
        field_simp [htan_ne_zero] at h11 ⊢
        <;> ring_nf <;> field_simp [htan_ne_zero]
        <;> norm_num
        <;> ring
        all_goals norm_num
        all_goals try { norm_num [htan_ne_zero] }
        all_goals try { tauto }
        all_goals try { 
          ring_nf at h11 ⊢; tauto
        }
      rw [this] at h11
      assumption
    assumption
  have htan2 : (1 - Real.tan θ) = (2 + Real.tan θ) := by
    have h_nonzero : 2 + Real.tan θ ≠ 0 := by
      by_contra h55
      have : (1 - Real.tan θ) / (2 + Real.tan θ) = 0 := by
        rw [h55]
        norm_num
        all_goals linarith
      linarith [htan2_simp, this]
    have h_nonzero' : (2 + Real.tan θ) ≠ 0 := h_nonzero
    field_simp [h_nonzero'] at htan2_simp ⊢
    <;> try { 
      linarith
      all_goals try { linarith }
      all_goals try { 
        nlinarith [Real.tan_sq_add_one θ, sq_pos_of_ne_zero (show (Real.tan θ : ℝ) ≠ 0 by assumption), sq_nonneg (Real.tan θ), sq_nonneg (2 + Real.tan θ)]
      }
    }
    <;> nlinarith [Real.tan_sq_add_one θ, sq_pos_of_ne_zero (show (Real.tan θ : ℝ) ≠ 0 by assumption), sq_nonneg (Real.tan θ), sq_nonneg (2 + Real.tan θ)]
  -- Solve for the value of tan θ.
  have htan_eq : Real.tan θ = -1 / 2 := by
    linarith
  have htan_eq' : Real.tan θ = Real.sin θ / Real.cos θ := by
    rw [Real.tan_eq_sin_div_cos]
  rw [htan_eq'] at htan_eq
  have hcos2 : Real.cos θ ^ 2 = 4 / 5 := by
    have hcos_ne_zero : Real.cos θ ≠ 0 := by
      by_contra hcos0
      rw [hcos0] at htan_eq
      norm_num at htan_eq
    have hsin2_eq : Real.sin θ = -1 / 2 * Real.cos θ := by
      field_simp [hcos_ne_zero] at htan_eq ⊢
      linarith
    have hsin2 : (Real.sin θ) ^ 2 + (Real.cos θ) ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    rw [hsin2_eq] at hsin2
    nlinarith [sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ - 0)]
  have hcos22 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := by
    rw [Real.cos_two_mul]
  rw [hcos22, hcos2]
  all_goals try norm_num
  all_goals try { 
    nlinarith
  }
  all_goals try { 
    assumption
  }
  all_goals try { 
    tauto
  }
  all_goals try { 
    norm_num
  }