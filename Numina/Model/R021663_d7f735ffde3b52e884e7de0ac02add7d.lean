import Mathlib

theorem number_theory_12351 : IsGreatest {x : ℤ | x > 0 ∧ ⌊(x / 7 : ℝ)⌋ = ⌊(x / 8 : ℝ)⌋ + 1} 104 := by
  constructor
  · -- Show that 104 is in the set.
    constructor
    · norm_num
    · -- Verify the equation for 104.
      norm_num
  · -- Show that 104 is the greatest element in the set
    intro x ⟨hx1, heq⟩
    by_contra h
    push_neg at h
    have h1' : x > 104 := by linarith
    have h2 : x ≥ 105 := by omega
    by_cases h6 : x ≤ 111
    · -- Assume x ≥ 105 and x ≤ 111.
      -- Prove a contradiction with heq.
      have h3 : x ≥ 105 := by omega
      have h4 : x ≤ 111 := by linarith
      have h7 : ⌊(x / (7 : ℝ))⌋ = 15 := by
        have h8 : x ≥ 105 := by omega
        have h9 : x ≤ 111 := by omega
        interval_cases x <;> norm_num
      have h8 : ⌊(x / (8 : ℝ))⌋ = 13 := by
        have h8 : x ≥ 105 := by omega
        have h9 : x ≤ 111 := by omega
        interval_cases x <;> norm_num
      rw [h7, h8] at heq
      all_goals omega
    · -- Now, let's address the case where x > 111, i.e. x ≥ 112.
      push_neg at h6
      have h6 : x > 111 := by omega
      have h7 : x ≥ 112 := by omega
      have h8 : x ≥ 112 := h7
      have h9 : (x : ℝ) ≥ (112 : ℝ) := by exact_mod_cast h7
      -- We can show that for x ≥ 112, floor(x/7) ≥ floor(x/8) + 2
      have h10 : (x / (7 : ℝ) ) ≥ (x / (8 : ℝ) ) + 2 := by 
        have h11 : (x : ℝ) ≥ (112 : ℝ) := by exact_mod_cast h7 
        have h12 : (x / (7 : ℝ) ) ≥ (x / (8 : ℝ) ) + 2 := by 
          have hx4 : (x : ℝ) / (7 : ℝ) - ( (x : ℝ) / (8 : ℝ) + (2 : ℝ) ) ≥ 0 := by 
            have : (x : ℝ) / (7 : ℝ) - ( (x : ℝ) / (8 : ℝ) + (2 : ℝ) ) = ( (x : ℝ) * 8 - (x : ℝ) * 7 - 112 ) / (56 : ℝ) := by 
              field_simp 
              <;> ring 
            rw [this] 
            apply div_nonneg 
            -- Show the numerator is non-negative 
            linarith 
            -- Show the denominator is positive 
            all_goals norm_num 
          linarith 
        linarith 
      have h13 : ⌊(x / (7 : ℝ) )⌋ ≥ ⌊(x / (8 : ℝ) )⌋ + 2 := by 
        have h11 : ⌊(x / (7 : ℝ) )⌋ ≥ ⌊( (x / (8 : ℝ) ) + (2 : ℝ) )⌋ := by 
          apply Int.floor_le_floor 
          linarith [h10] 
        have h14 : ⌊( (x / (8 : ℝ) ) + (2 : ℝ) )⌋ = ⌊(x / (8 : ℝ) )⌋ + 2 := by 
          norm_num [Int.floor_eq_iff] 
          <;> ( 
            try { 
              have h15 : (x : ℝ) / (8 : ℝ) + (2 : ℝ) ≥ (⌊(x / (8 : ℝ) )⌋ + 2 : ℝ) := by 
                have h16 : (x / (8 : ℝ) ) ≥ (⌊(x / (8 : ℝ) )⌋ : ℝ) := by 
                  exact_mod_cast (Int.floor_le (x / (8 : ℝ) ) ) 
                nlinarith 
              linarith 
            } 
          ) 
          <;> ( 
            try { 
              have h17 : (⌊(x / (8 : ℝ) )⌋ + 2 : ℝ) + (1 : ℝ) > (x / (8 : ℝ) ) + (2 : ℝ) := by 
                have h18 : (⌊(x / (8 : ℝ) )⌋ + 1 : ℝ) > (x / (8 : ℝ) ) := by 
                  exact_mod_cast (Int.lt_floor_add_one (x / (8 : ℝ) ) ) 
                nlinarith 
              linarith 
            } 
          ) 
        linarith [h11, h14] 
      linarith [h13, heq]