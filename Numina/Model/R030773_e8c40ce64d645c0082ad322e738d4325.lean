import Mathlib

theorem algebra_5501 : IsLeast {x : ℕ | (Real.sqrt 5 + Real.sqrt 3)^6 < x} 3904 := by 
  constructor 
  · -- Show 3904 is in the set 
    have h1 : (Real.sqrt 5 + Real.sqrt 3 : ℝ) ^ 2 = 8 + 2 * Real.sqrt 15 := by 
      have h2 : Real.sqrt 5 ^ 2 = (5 : ℝ) := by 
        rw [Real.sq_sqrt] 
        norm_num 
      have h3 : Real.sqrt 3 ^ 2 = (3 : ℝ) := by 
        rw [Real.sq_sqrt] 
        norm_num 
      have h4 : Real.sqrt 5 * Real.sqrt 3 = Real.sqrt 15 := by 
        have h5 : Real.sqrt 5 * Real.sqrt 3 = Real.sqrt (5 * (3 : ℝ)) := by 
          rw [Real.sqrt_mul] 
          all_goals norm_num 
        rw [h5] 
        all_goals 
        ring_nf 
      nlinarith [h2, h3, Real.sqrt_nonneg 5, Real.sqrt_nonneg 3, h4, Real.sqrt_nonneg 15] 
    have h2 : (Real.sqrt 5 + Real.sqrt 3 : ℝ) ^ 6 = (8 + 2 * Real.sqrt 15) ^ 3 := by 
      calc 
        (Real.sqrt 5 + Real.sqrt 3 : ℝ) ^ 6 = ((Real.sqrt 5 + Real.sqrt 3) ^ 2) ^ 3 := by ring 
        _ = (8 + 2 * Real.sqrt 15) ^ 3 := by 
          rw [h1] 
    rw [h2] 
    have h3 : Real.sqrt 15 ^ 2 = (15 : ℝ) := by
      rw [Real.sq_sqrt]
      norm_num
    have h4 : (8 + 2 * Real.sqrt 15 : ℝ) ^ 3 < (3904 : ℝ) := by 
      nlinarith [h3, Real.sqrt_nonneg 15, 
        sq_nonneg (Real.sqrt 15: ℝ), 
          Real.sqrt_nonneg 5, 
            Real.sqrt_nonneg 3, 
              sq_nonneg (Real.sqrt 5: ℝ), 
                sq_nonneg (Real.sqrt 3: ℝ)
      ]
    exact_mod_cast h4 
  · -- Show that 3904 is minimal 
    intro x hx
    norm_num at hx ⊢ 
    have h1 : (Real.sqrt 5 + Real.sqrt 3 : ℝ) ^ 2 = 8 + 2 * Real.sqrt 15 := by 
      have h2 : Real.sqrt 5 ^ 2 = (5 : ℝ) := by 
        rw [Real.sq_sqrt] 
        norm_num 
      have h3 : Real.sqrt 3 ^ 2 = (3 : ℝ) := by 
        rw [Real.sq_sqrt] 
        norm_num 
      have h4 : Real.sqrt 5 * Real.sqrt 3 = Real.sqrt 15 := by 
        have h5 : Real.sqrt 5 * Real.sqrt 3 = Real.sqrt (5 * (3 : ℝ)) := by 
          rw [Real.sqrt_mul] 
          all_goals norm_num 
        rw [h5] 
        all_goals 
        ring_nf 
      nlinarith [h2, h3, Real.sqrt_nonneg 5, Real.sqrt_nonneg 3, h4, Real.sqrt_nonneg 15] 
    have h2 : (Real.sqrt 5 + Real.sqrt 3 : ℝ) ^ 6 = (8 + 2 * Real.sqrt 15) ^ 3 := by 
      calc 
        (Real.sqrt 5 + Real.sqrt 3 : ℝ) ^ 6 = ((Real.sqrt 5 + Real.sqrt 3) ^ 2) ^ 3 := by ring 
        _ = (8 + 2 * Real.sqrt 15) ^ 3 := by 
          rw [h1] 
    have h3 : (Real.sqrt 5 + Real.sqrt 3 : ℝ) ^ 6 ≥ (3903 : ℝ) := by 
      rw [h2]
      nlinarith [sq_nonneg (Real.sqrt 15: ℝ), Real.sqrt_nonneg 15, 
        Real.sqrt_nonneg 5, 
        Real.sqrt_nonneg 3, 
        sq_nonneg (Real.sqrt 5: ℝ), 
        sq_nonneg (Real.sqrt 3: ℝ),
        Real.sq_sqrt (show 0 ≤ (15 : ℝ) by norm_num)
      ]
    have h4 : x ≥ 3904 := by 
      by_contra h 
      push_neg at h 
      have h5 : x ≤ 3903 := by 
        omega 
      have h6 : (Real.sqrt 5 + Real.sqrt 3 : ℝ) ^ 6 ≥ (3903 : ℝ) := h3 
      have h7 : (Real.sqrt 5 + Real.sqrt 3 : ℝ) ^ 6 < (x : ℝ) := by 
        exact_mod_cast hx 
      have h8 : (3903 : ℝ) < (x : ℝ) := by 
        nlinarith 
      have h9 : (3903 : ℝ) ≥ (x : ℝ) := by 
        have h10 : x ≤ 3903 := by omega 
        have h11 : (x : ℝ) ≤ (3903 : ℝ) := by exact_mod_cast h10 
        linarith 
      linarith 
    omega