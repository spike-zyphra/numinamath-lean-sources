import Mathlib

open Real

theorem algebra_224766 {x : ℝ} (hx : 0 < x) :
    (logb 10 x)^2015 < (logb 10 x)^2014 ∧ (logb 10 x)^2014 < (logb 10 x)^2016 ↔
    x ∈ Set.Ioo 0 (1 / 10) := by
  constructor
  · -- Forward direction: if the inequalities hold, then x is in (0, 1/10)
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 : x ∈ Set.Ioo 0 (1 / 10) := by
      constructor
      · -- Show 0 < x
        exact hx
      · -- Assume x ≥ 1/10 to get a contradiction
        by_contra h4
        push_neg at h4
        have h5 : logb 10 x ≥ -1 := by
          have h6 : x ≥ (1 / 10 : ℝ) := by linarith
          have h7 : logb 10 x ≥ logb 10 (1 / 10 : ℝ) := by
            apply Real.logb_le_logb_of_le
            all_goals try linarith
          have h8 : logb 10 (1 / 10 : ℝ) = -1 := by
            simp [Real.logb_eq_iff_rpow_eq]
          linarith [h7, h8]
        -- positivity is here to show non-negativity after all
        have h2014_nonneg : (logb 10 x) ^ 2014 ≥ 0 := by
          have hx6_pos : logb 10 x ≥ -1 := h5
          have h11_pos : (logb 10 x) ^ 2 ≥ 0 := by nlinarith
          have h2014_pos : (logb 10 x) ^ 2014 = ((logb 10 x) ^ 2) ^ 1007 := by
            ring_nf
          rw [h2014_pos]
          have h_nonneg : ((logb 10 x) ^ 2) ^ 1007 ≥ 0 := by 
            apply pow_nonneg 
            linarith -- using h11_pos factored
            all_goals try { nlinarith } 
            all_goals try { tauto } 
          linarith
        have h9 : (logb 10 x) ^ 2014 * (logb 10 x - 1) < 0 := by 
          have h31 : logb 10 x - 1 ≤ -2 := by
            nlinarith 
          have h32 : (logb 10 x) ^ 2014 ≥ 0 := h2014_nonneg
          have h33 : (logb 10 x) ^ 2014 * (logb 10 x - 1) < 0 := by
            have h_11_pos : logb 10 x ≤ -1 := by linarith
            have h_11_pos_2 : logb 10 x < (0 : ℝ) := by linarith
            have h10_pos : logb 10 x ≠ 0 := by linarith
            have h11_pos2 : (logb 10 x) ^ 2014 > 0 := by 
              have h12_pos2 : logb 10 x ≠ 0 := h10_pos
              have h13_pos : logb 10 x < 0 := h_11_pos_2
              have h_pos : (logb 10 x) ^ 2 > 0 := by 
                nlinarith 
              have h2014_pos_2 : (logb 10 x) ^ 2014 = ((logb 10 x) ^ 2) ^ 1007 := by 
                ring_nf 
              rw [h2014_pos_2] 
              positivity
            apply mul_neg_of_pos_of_neg
            linarith 
            nlinarith 
          assumption
        have h10 : (logb 10 x) ^ 2 - 1 ≤ 0 := by
          nlinarith [sq_nonneg (logb 10 x + 1), sq_nonneg (logb 10 x - 1)]
        have h11 : (logb 10 x) ^ 2014 * ((logb 10 x) ^ 2 - 1) ≤ 0 := by
          have h3_pos : (logb 10 x) ^ 2014 ≥ 0 := h2014_nonneg
          have h4_pos : (logb 10 x) ^ 2 - 1 ≤ 0 := h10
          nlinarith [h3_pos, h4_pos]
        have h12 : (logb 10 x) ^ 2014 * ((logb 10 x) ^ 2 - 1) > 0 := by
          nlinarith
        linarith 
    exact h3
  · -- Backward direction: if x ∈ (0, 1/10), then the inequalities hold
    intro h
    rcases h with ⟨hx1, hx2⟩
    have h5 : logb 10 x < -1 := by
      have h6 : x < (1 / 10 : ℝ) := by linarith
      have h7 : logb 10 x < logb 10 (1 / 10 : ℝ) := by
        apply Real.logb_lt_logb 
        all_goals try linarith
      have h8 : logb 10 (1 / 10 : ℝ) = -1 := by 
        simp [Real.logb_eq_iff_rpow_eq]
      linarith
    -- positivity is here to show strict greater zero.
    have h3_pos : (logb 10 x) ^ 2014 > 0 := by
      have h11_pos : logb 10 x < -1 := h5
      have h10_pos : logb 10 x < 0 := by linarith
      have h10_pos_2 : logb 10 x ≠ 0 := by linarith
      have h11_pos2 : (logb 10 x) ^ 2014 > 0 := by 
        have h13_pos : logb 10 x ≠ 0 := h10_pos_2
        have h1_12_pos : logb 10 x < 0 := h10_pos
        have h14_pos : (logb 10 x) ^ 2 > 0 := by 
          nlinarith
        have h2014_pos : (logb 10 x) ^ 2014 = ((logb 10 x) ^ 2) ^ 1007 := by 
          ring_nf 
        rw [h2014_pos]
        positivity
      linarith
    -- Now prove the first inequality.
    have h1 : (logb 10 x)^2015 < (logb 10 x)^2014 := by
      have h4 : (logb 10 x)^2014 * (logb 10 x - 1) < 0 := by
        have h11 : (logb 10 x) - 1 < -2 := by
          nlinarith
        have h12 : (logb 10 x)^2014 > 0 := h3_pos
        nlinarith
      have h5 : (logb 10 x)^2015 = (logb 10 x)^2014 * (logb 10 x) := by
        ring
      have h6 : (logb 10 x)^2014 = (logb 10 x)^2014 := by
        rfl
      nlinarith
    -- Now prove the second inequality.
    have h2 : (logb 10 x)^2014 < (logb 10 x)^2016 := by
      have h4 : (logb 10 x)^2014 * ((logb 10 x)^2 - 1) > 0 := by
        have h11 : (logb 10 x)^2 > 1 := by
          nlinarith
        have h12 : (logb 10 x) ^ 2014 > 0 := h3_pos
        nlinarith
      have h1' : (logb 10 x)^2016 = (logb 10 x)^2014 * ((logb 10 x)^2) := by
        ring
      rw [h1']
      nlinarith
    exact ⟨h1, h2⟩