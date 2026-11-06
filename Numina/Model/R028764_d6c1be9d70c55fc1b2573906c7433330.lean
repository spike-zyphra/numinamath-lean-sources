import Mathlib

theorem number_theory_1557 (a b c : ℤ) (h₀ : 0 ≤ |a - b| ^ 19 ) (h₁ : 0 ≤ |c - a| ^ 95)
    (h₂ : |a - b| ^ 19 + |c - a| ^ 95 = 1) :
    |c - a| + |a - b| + |b - c| = 2 := by 
  have h3 : |a - b| ^ 19 ≤ 1 := by 
    linarith 
  have h4 : |a - b| ≤ 1 := by 
    by_contra h 
    push_neg at h 
    have h5 : |a - b| ^ 19 ≥ 2 ^ 19 := by
      have h6 : |a - b| ≥ 2 := by 
        omega 
      have h7 : |a - b| ^ 19 ≥ 2 ^ 19 := by 
        apply pow_le_pow_left 
        all_goals linarith 
      linarith 
    nlinarith 
  have h5 : |a - b| = 0 ∨ |a - b| = 1 := by 
    have h6 : |a - b| ≥ 0 := by 
      apply abs_nonneg 
    interval_cases h : |a - b| <;> omega 
  have h8 : |c - a| ≤ 1 := by 
    by_contra h 
    push_neg at h 
    have h9 : |c - a| ^ 95 ≥ 2 ^ 95 := by 
      have h10 : |c - a| ≥ 2 := by 
        omega 
      have h11 : |c - a| ^ 95 ≥ 2 ^ 95 := by 
        apply pow_le_pow_left 
        all_goals linarith 
      linarith 
    nlinarith 
  have h9 : |c - a| = 0 ∨ |c - a| = 1 := by 
    have h10 : |c - a| ≥ 0 := by 
      apply abs_nonneg 
    interval_cases h : |c - a| <;> omega 
  rcases h5 with h5 | h5 
  · -- Case |a - b| = 0 
    rcases h9 with h9 | h9 
    · -- Case |c - a| = 0 
      exfalso 
      rw [show |a - b| = 0 by linarith [h5], show |c - a| = 0 by linarith [h9]] at h₂ 
      all_goals 
        norm_num at h₂ 
    · -- Case |c - a| = 1 
      have h0 : |a - b| = 0 := by 
        omega 
      have h13 : |c - a| = 1 := by 
        omega 
      have h14 : a - b = 0 := by 
        have h15 : |a - b| = 0 := by 
          omega 
        cases' abs_cases (a - b) with h h 
        all_goals 
          omega 
      have h17 : a = b := by 
        linarith 
      have h18 : |b - c| = 1 := by 
        have h19 : |b - c| = |c - a| := by 
          have h20 : b - c = -(c - a) := by 
            have h23 : a = b := h17 
            have h24 : b - c = a - c := by 
              omega 
            have h25 : a - c = -(c - a) := by 
              omega 
            omega 
          have h22 : |b - c| = |c - a| := by 
            rw [h20] 
            rw [abs_neg] 
          exact h22 
        have h13 : |c - a| = 1 := by 
          omega 
        linarith [h19, h13] 
      linarith [h13, h0, h18] 
  · -- Case |a - b| = 1 
    rcases h9 with h9 | h9 
    · -- Case |c - a| = 0 
      have h15 : |a - b| = 1 := by 
        omega 
      have h16 : |c - a| = 0 := by 
        omega 
      have h17 : c - a = 0 := by 
        cases' abs_cases (c - a) with h h 
        all_goals 
          omega 
      have h18 : c = a := by 
        linarith 
      have h19 : |b - c| = 1 := by 
        have h20 : |b - c| = |b - a|  := by 
          rw [show c = a by omega]
        have h22 : |b - a| = 1 := by 
          have h23 : |a - b| = 1 := by 
            omega 
          have h24 : |b - a| = |a - b|  := by 
            rw [show b - a = -(a - b) by omega]
            rw [abs_neg] 
          rw [h24] 
          all_goals 
            linarith 
        rw [h20] 
        exact h22 
      linarith [h16, h15, h19] 
    · -- Case |c - a| = 1 
      exfalso 
      have h16 : |c - a| = 1 := by 
        omega 
      have h17 : |a - b| ^ 19 + |c - a| ^ 95 = 1 := h₂
      rw [show |a - b| = 1 by omega, show |c - a| = 1 by omega] at h17 
      all_goals 
        norm_num at h17