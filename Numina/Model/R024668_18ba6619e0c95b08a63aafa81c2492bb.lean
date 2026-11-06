import Mathlib

theorem number_theory_239612 (n : ℕ) :
    IsLeast {n | ∃ x : ℕ, x > 0 ∧ ⌊(10^n / x : ℝ)⌋ = 2006} 7 := by
  constructor 
  · -- Show that 7 is in the set.
    use 4984
    norm_num
  · -- Show that 7 is the minimum.
    intro n hn
    rcases hn with ⟨x, hx_pos, hfloor⟩
    by_contra h
    push_neg at h
    have h1 : n < 7 := h 
    -- Let's get a tighter upper bound on x than 5000.
    have h4 : 10 ^ n < 2007 * x := by
      have h4 : ⌊(10 ^ n / (x : ℝ) : ℝ)⌋ = (2006 : ℤ) := by 
        simpa using hfloor 
      have h5 : ( (10 ^ n / (x : ℝ) : ℝ) ) < (2007 : ℝ) := by 
        have h7 : ⌊(10 ^ n / (x : ℝ) : ℝ)⌋ = (2006 : ℤ) := by
          simpa using h4 
        have h8 : (10 ^ n / (x : ℝ) : ℝ) < (⌊(10 ^ n / (x : ℝ) : ℝ)⌋ + 1 : ℝ) := by
          exact_mod_cast Int.lt_floor_add_one (10 ^ n / (x : ℝ) : ℝ) 
        rw [show (⌊(10 ^ n / (x : ℝ) : ℝ)⌋ : ℝ) = (2006 : ℝ) by exact_mod_cast h7] at h8
        nlinarith 
      have h7 : (x : ℝ) > (0 : ℝ) := by 
        exact_mod_cast (show x > 0 by linarith [hx_pos] ) 
      have h8 : (10 ^ n : ℝ) < (2007 : ℝ) * (x : ℝ) := by
        have h9 : (x : ℝ) > 0 := by
          exact_mod_cast hx_pos
        have h10 : (10 ^ n / (x : ℝ) : ℝ) < (2007 : ℝ) := h5
        have h11 : (10 ^ n / (x : ℝ) : ℝ) * (x : ℝ) < (2007 : ℝ) * (x : ℝ) := by
          apply mul_lt_mul_of_pos_right 
          all_goals linarith 
        have h12 : (10 ^ n / (x : ℝ) : ℝ) * (x : ℝ) = (10 ^ n : ℝ) := by
          field_simp 
        linarith 
      exact_mod_cast h8 
    have h5 : 2006 * x ≤ 10 ^ n := by
      have h4 : ⌊(10 ^ n / (x : ℝ) : ℝ)⌋ = (2006 : ℤ) := by 
        simpa using hfloor
      have h5 : ( (10 ^ n / (x : ℝ) : ℝ) ) ≥ (2006 : ℝ) := by
        have h6 : ( (10 ^ n / (x : ℝ) : ℝ) ) ≥ (⌊(10 ^ n / (x : ℝ) : ℝ)⌋ : ℝ) := by 
          simp [Int.floor_le] 
        rw [show (⌊(10 ^ n / (x : ℝ) : ℝ)⌋ : ℝ) = (2006 : ℝ) by
          exact_mod_cast (show ⌊(10 ^ n / (x : ℝ) : ℝ)⌋ = (2006 : ℤ) by linarith [h4]
          )] at h6
        linarith 
      have h7 : (x : ℝ) > 0 := by
        exact_mod_cast (show x > 0 by linarith [hx_pos] ) 
      have h8 : (10 ^ n : ℝ) ≥ (2006 : ℝ) * (x : ℝ) := by
        have h9 : (x : ℝ) > 0 := by
          exact_mod_cast hx_pos
        have h10 : (10 ^ n / (x : ℝ) : ℝ) ≥ (2006 : ℝ) := h5
        have h11 : (10 ^ n / (x : ℝ) : ℝ) * (x : ℝ) ≥ (2006 : ℝ) * (x : ℝ) := by
          apply mul_le_mul_of_nonneg_right 
          all_goals linarith 
        have h12 : (10 ^ n / (x : ℝ) : ℝ) * (x : ℝ) = (10 ^ n : ℝ) := by
          field_simp 
        linarith 
      exact_mod_cast h8 
    have h6 : n < 7 := h1 
    have h7 : n ≤ 6 := by 
      omega 
    -- Now, let's use interval_cases on n. This will discharge all the goals.
    interval_cases n <;> try { 
      omega 
    } <;> try { 
      norm_num at h5 h4 hfloor 
      all_goals
        try { 
          have h8' : x ≤ 3000 := by
            nlinarith 
          interval_cases x <;> norm_num at hfloor h5 h4 
        } 
    }