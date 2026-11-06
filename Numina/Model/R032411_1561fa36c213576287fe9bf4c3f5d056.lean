import Mathlib

open Real

theorem inequalities_186857 (x : ℝ) (hx : x ≠ -3) :
    2 / (x + 3) - 1 / 2 ≥ 5 / (x + 3) - 1 / 10 ↔ -10.5 ≤ x ∧ x < -3 := by
  constructor
  · -- Forward direction: If the inequality holds, prove -10.5 ≤ x ∧ x < -3
    intro h
    have h1 : x + 3 ≠ 0 := by
      by_contra h2
      have h2 : x = -3 := by linarith 
      tauto
    have h2 : 2 / (x + 3) - 1 / 2 - (5 / (x + 3) - 1 / 10) ≥ 0 := by linarith 
    have h3 : -3 / (x + 3) - (2 / 5) ≥ 0 := by
      have h4 : (2 / (x + 3) - 1 / 2 - (5 / (x + 3) - 1 / 10) : ℝ) =
          -3 / (x + 3) - (2 / 5) := by 
        field_simp [h1]
        <;> linarith 
      linarith [h4, h2]
    
    by_cases h4 : x + 3 > 0 
    · -- If x + 3 > 0, which leads to a contradiction.
      -- h3 is -3 / (x+3) - 2/5 ≥ 0 in hypothesis.
      -- Multiply through by x+3 >0
      -- obtain -3 - (2/5)(x+3) >=0
      -- i.e. -3 >= (2/5)(x+3)
      -- Multiply by 5: -15 >= 2(x+3)
      -- i.e. -15 >= 2x+6
      -- i.e. -21 >= 2x
      -- i.e. -10.5 >= x
      -- but we have x+3 >0, i.e., x > -3
      -- which is impossible if -10.5 >=x.
      -- The precise way how the Lean code must handle.
      -- This is inconsistency.
      have h5 : -3 / (x + 3) ≥ (2 / 5 : ℝ) := by
        linarith [h3]
      have h6 : -3 ≥ (2 / 5 * (x + 3) : ℝ) := by
        have pos1 : x + 3 > 0 := h4
        have h10 : (x + 3 : ℝ) > 0 := h4
        have h7' : -3 / (x + 3) = (-3 : ℝ) / (x + 3) := by ring_nf
        rw [h7'] at h5
        have h8 : (-3 : ℝ) / (x + 3) ≥ (2 / 5 : ℝ) := by linarith
        have h12 : (x + 3 : ℝ) > 0 := h4
        have h13 : (-3 : ℝ) ≥ (2 / 5 * (x + 3) : ℝ) := by
          apply (le_div_iff₀ (by linarith)).mp at h8 
          linarith 
        linarith 
      nlinarith
    · -- Case x + 3 ≤ 0
      by_cases h5 : x + 3 < (0 : ℝ)
      · -- Case x + 3 < 0
        constructor
        · -- Prove -10.5 ≤ x
          have h7 : -3 / (x + 3) ≥ (2 / 5 : ℝ) := by 
            linarith [h3]
          have h8 : -3 ≤ (2 / 5 * (x + 3) : ℝ) := by 
            have h9 : (x + 3 : ℝ) < (0 : ℝ) := h5
            have h7' : -3 / (x + 3) = (-3 : ℝ) / (x + 3) := by ring_nf
            rw [h7'] at h7
            have h12 : (-3 : ℝ) / (x + 3) ≥ (2 / 5 : ℝ) := by linarith 
            have h11 : (x + 3 : ℝ) < (0 : ℝ) := h5
            have h13 : (-3 : ℝ) ≤ (2 / 5 * (x + 3) : ℝ) := by 
              apply (le_div_iff_of_neg' (by linarith)).mp at h12 
              linarith 
            linarith 
          nlinarith
        · -- Prove x < -3
          have h7 : -3 / (x + 3) ≥ (2 / 5 : ℝ) := by 
            linarith [h3]
          have h8 : -3 ≤ (2 / 5 * (x + 3) : ℝ) := by
            have h9 : (x + 3 : ℝ) < (0 : ℝ) := h5
            have h7' : -3 / (x + 3) = (-3 : ℝ) / (x + 3) := by ring_nf
            rw [h7'] at h7
            have h12 : (-3 : ℝ) / (x + 3) ≥ (2 / 5 : ℝ) := by linarith 
            have h11 : (x + 3 : ℝ) < (0 : ℝ) := h5
            have h13 : (-3 : ℝ) ≤ (2 / 5 * (x + 3) : ℝ) := by 
              apply (le_div_iff_of_neg' (by linarith)).mp at h12 
              linarith 
            linarith 
          nlinarith
      · -- Case x + 3 = 0, which is a contradiction
        have h6 : x + 3 = 0 := by
          linarith 
        have h7 : x = -3 := by
          linarith 
        tauto 
  · -- Backward: From -10.5 ≤ x ∧ x < -3, prove the inequality 
    rintro ⟨h1, h2⟩
    have h3 : x + 3 < (0 : ℝ) := by 
      linarith 
    have h4 : 2 / (x + 3) - 1 / 2 - (5 / (x + 3) - 1 / 10) ≥ 0 := by
      have h5 : x + 3 < 0 := h3 
      have h6 : 2 / (x + 3) - 1 / 2 - (5 / (x + 3) - 1 / 10) = -3 / (x + 3) - (2 / 5 : ℝ) := by 
        field_simp [(show (x + 3) ≠ 0 by
          by_contra h11
          have h22 : x = -3 := by linarith 
          tauto 
        )]
        <;> ring_nf <;> field_simp [(show (x + 3) ≠ 0 by
          by_contra h11
          have h22 : x = -3 := by linarith 
          tauto 
        )]
        <;> ring 
      rw [h6] 
      have h7 : -3 / (x + 3) - (2 / 5 : ℝ) ≥ 0 := by 
        have h8 : x + 3 < 0 := h3
        have h9 : -3 / (x + 3) = (-3 : ℝ) / (x + 3) := by ring_nf 
        rw [h9] 
        have h10 : (-3 : ℝ) / (x + 3) ≥ (2 / 5 : ℝ) := by 
          have h11 : (x + 3 : ℝ) < (0 : ℝ) := h3 
          have h12 : (-3 : ℝ) ≤ (2 / 5 * (x + 3) : ℝ) := by 
            nlinarith 
          have h6 : (-3 : ℝ) / (x + 3) ≥ (2 / 5 : ℝ) := by 
            have h18 : (x + 3) < (0 : ℝ) := h3 
            apply (le_div_iff_of_neg' (by linarith)).mpr 
            linarith 
          linarith 
        linarith 
      linarith 
    linarith