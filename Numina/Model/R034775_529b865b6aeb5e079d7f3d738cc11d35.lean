import Mathlib

theorem algebra_9385 {f : ℝ → ℝ} (hf : StrictMono f)
    (h : ∀ x, f (f x - 3 ^ x) = 4) :
    f (Real.logb 3 9) = 10 := by
  have h1 : Real.logb 3 9 = 2 := by 
    rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
  have h1' : f (f 0 - 1) = 4 := by 
    specialize h 0 
    norm_num at h ⊢ 
    linarith 
  have h2 : f (f 1 - 3) = 4 := by 
    specialize h 1 
    norm_num at h ⊢ 
    linarith 
  have h3 : f 0 - 1 = f 1 - 3 := by 
    have h4 : f (f 0 - 1) = f (f 1 - 3) := by linarith [h1', h2]
    exact hf.injective h4
  have h4' : f 1 = f 0 + 2 := by 
    nlinarith 
  have h4 : f (f 2 - 9) = 4 := by 
    specialize h 2 
    norm_num at h ⊢ 
    linarith 
  have h5 : f 2 - 9 = f 0 - 1 := by 
    by_contra h'
    push_neg at h'
    have h_eq : f (f 2 - 9) = f (f 0 - 1) := by 
      linarith [h4, h1']
    have h4 : f 2 - 9 = f 0 - 1 := by 
      apply hf.injective 
      all_goals 
      linarith [h_eq]
    exfalso
    have h₀ : f 2 - 9 = f 0 - 1 := by linarith [h4]
    tauto 
  have h6 : f (f (f 0 - 1) - 3 ^ (f 0 - 1 : ℝ)) = 4 := by
    specialize h (f 0 - 1)
    simpa using h
  have eq2 : f 0 = (2 : ℝ) := by 
    have eq3 : 4 - (3 : ℝ) ^ (f 0 - 1 : ℝ) = f 0 - 1 := by 
      have eq4 : f (f 0 - 1 : ℝ) - 3 ^ (f 0 - 1 : ℝ) = f 0 - 1 := by 
        have eq5 : f (f (f 0 - 1 : ℝ) - 3 ^ (f 0 - 1 : ℝ) ) = 4 := by 
          linarith [h6, h1']
        have eq7 : f (f 0 - 1 : ℝ) = 4 := by 
          linarith [h1']
        have eq8 : f (f (f 0 - 1 : ℝ) - 3 ^ (f 0 - 1 : ℝ) ) = f (f 0 - 1 : ℝ) := by 
          linarith [eq5, eq7]
        have eq9 : (f (f 0 - 1 : ℝ) - 3 ^ (f 0 - 1 : ℝ) ) = (f 0 - 1 : ℝ) := by 
          apply hf.injective 
          linarith [eq8]
        have eq10 : f (f 0 - 1 : ℝ) = 4 := by
          linarith [h1']
        nlinarith [eq9, eq10]
      linarith
    have eq5 : f 0 - 1 = (1 : ℝ) := by
      by_cases h' : f 0 - 1 < (1 : ℝ)
      · -- Assume f 0 - 1 < 1
        have eq8 : f 0 - 1 = (1 : ℝ) := by 
          have eq5 : 4 - (3 : ℝ) ^ (f 0 - 1 : ℝ) = f 0 - 1 := eq3 
          have eq13 : (3 : ℝ) ^ (f 0 - 1 : ℝ) < (3 : ℝ) := by
            have h' : f 0 - 1 < (1 : ℝ) := h'
            have h7 : (3 : ℝ) ^ (f 0 - 1 : ℝ) < (3 : ℝ) ^ (1 : ℝ) := by 
              apply Real.rpow_lt_rpow_of_exponent_lt 
              all_goals nlinarith 
            norm_num at h7 ⊢ 
            linarith 
          nlinarith [eq5, eq13]
        linarith 
      · -- Case where f 0 - 1 ≥ 1
        have h7 : f 0 - 1 ≥ (1 : ℝ) := by linarith 
        have eq8 : f 0 - 1 = (1 : ℝ) := by 
          have eq5 : 4 - (3 : ℝ) ^ (f 0 - 1 : ℝ) = f 0 - 1 := eq3 
          have eq13 : (3 : ℝ) ^ (f 0 - 1 : ℝ) ≥ (3 : ℝ) := by 
            have h7 : f 0 - 1 ≥ (1 : ℝ) := by linarith 
            have h7' : (3 : ℝ) ^ (f 0 - 1 : ℝ) ≥ (3 : ℝ) ^ (1 : ℝ) := by 
              apply Real.rpow_le_rpow_of_exponent_le 
              all_goals nlinarith 
            norm_num at h7' ⊢ 
            linarith 
          nlinarith [eq5, eq13]
        linarith 
    linarith 
  have eq6 : f 2 = (10 : ℝ) := by 
    nlinarith [h5, eq2]
  rw [h1] 
  exact_mod_cast eq6