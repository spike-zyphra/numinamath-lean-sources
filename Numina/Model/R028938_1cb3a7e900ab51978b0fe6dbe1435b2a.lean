import Mathlib

theorem algebra_297719 (x : ℝ) (h : Real.sin x = (1 - abs (Real.cos x)) / (1 + abs (Real.cos x))) :
    ∃ k : ℤ, x = k * Real.pi ∨ x = 2 * k * Real.pi + Real.pi / 2 := by
  by_cases h2 : 1 + abs (Real.cos x) = 0
  · -- The case where 1 + abs (Real.cos x) = 0 is impossible.
    have h30 : abs (Real.cos x) = -1 := by linarith
    have h31 : abs (Real.cos x) ≥ 0 := abs_nonneg (Real.cos x)
    linarith
  · -- Denominator `1 + abs (Real.cos x)` is non-zero.
    have h_eq1 : Real.sin x * (1 + abs (Real.cos x)) = 1 - abs (Real.cos x) := by
      have h30 : 1 + abs (Real.cos x) ≠ 0 := by
        by_contra h31
        have h32 : 1 + abs (Real.cos x) = 0 := by linarith
        tauto
      field_simp [h30] at h ⊢
      <;> nlinarith
      all_goals linarith
    have h_eq3 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    have h_eq4 : abs (Real.cos x) ^ 2 = Real.cos x ^ 2 := by
      simp [abs_pow]
      all_goals nlinarith
    have h_eq5 : Real.sin x ^ 2 = 1 - abs (Real.cos x) ^ 2 := by
      have eq9 : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
        linarith [h_eq3]
      have eq9b : Real.cos x ^ 2 = abs (Real.cos x) ^ 2 := by
        nlinarith [h_eq4]
      nlinarith
    by_cases h5 : abs (Real.cos x) = 1
    · -- Case 5a: |cos x| = 1
      have h6 : Real.sin x = 0 := by
        rw [show abs (Real.cos x) = (1 : ℝ) by nlinarith] at h_eq1
        nlinarith
      have h8 : ∃ k : ℤ, x = k * Real.pi := by
        have h20 : Real.sin x = 0 := h6
        obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 h20
        use k
        all_goals try simp [hk] at *
        all_goals try tauto
      rcases h8 with ⟨k, hk⟩
      use k
      left
      linarith
    · -- Case 5b: abs (Real.cos x) ≠ 1. So abs (Real.cos x) < 1
      have h5a : abs (Real.cos x) < 1 := by
        by_contra h6
        push_neg at h6
        have h6_1 : abs (Real.cos x) = 1 := by
          have h611 : abs (Real.cos x) ≤ 1 := by
            apply abs_le.mpr
            constructor <;> nlinarith [Real.cos_sq_add_sin_sq x, sq_nonneg (Real.sin x)]
          have h612 : abs (Real.cos x) ≥ 1 := by
            by_contra h613
            push_neg at h613
            have : abs (Real.cos x) < (1 : ℝ) := by nlinarith
            linarith [abs_nonneg (Real.cos x)]
          have h613 : abs (Real.cos x) = 1 := by
            nlinarith
          assumption
        tauto
      have h6 : abs (Real.cos x) = 0 := by
        nlinarith [sq_nonneg (Real.sin x * abs (Real.cos x)), sq_nonneg (Real.sin x ^ 2 - (1 - abs (Real.cos x) ^ 2)), sq_nonneg (abs (Real.cos x) ^ 2 - 0), sq_nonneg (Real.sin x ^ 2 - 0)]
      have hc2 : Real.cos x = 0 := by
        rw [abs_eq_zero] at h6
        linarith
      have h13 : Real.sin x = 1 := by
        rw [hc2] at h_eq1
        simp at h_eq1
        nlinarith
      have hk : ∃ k : ℤ, x = 2 * k * Real.pi + Real.pi / 2 := by
        have h14 : Real.sin x = 1 := h13
        have h15 : ∃ k : ℤ, x = Real.pi / 2 + 2 * k * Real.pi := by
          rw [Real.sin_eq_one_iff] at h14
          obtain ⟨k, hk⟩ := h14
          use k
          try { 
            linarith 
          }
          all_goals try { 
            nlinarith 
          }
        rcases h15 with ⟨k, hk⟩
        use k
        all_goals try { 
          nlinarith [Real.pi_pos] 
        }
      rcases hk with ⟨k, hk⟩
      use k
      right
      linarith
      all_goals try { 
        nlinarith 
      }