import Mathlib

theorem algebra_14972 {a b : ℤ} (ha : a < Real.logb 10 28471) (hb : Real.logb 10 28471 < b)
    (hab : ∃ n, a = n ∧ b = n + 1) : a + b = 9 := by

  rcases hab with ⟨n, h1, h2⟩
  have hb_rw : Real.logb 10 28471 < (↑(n + 1) : ℝ) := by 
    have : (↑b : ℝ) = (↑(n + 1) : ℝ) := by exact_mod_cast h2
    rw [this] at hb
    linarith
  have h7 : 4 < Real.logb 10 28471 := by
    have h8 : Real.logb 10 28471 > 4 := by
      have h9 : Real.logb 10 28471 > Real.logb 10 (10000 : ℝ) := by
        apply Real.logb_lt_logb
        all_goals norm_num
      have h10 : Real.logb 10 (10000 : ℝ) = 4 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      linarith
    linarith
  have h10 : Real.logb 10 28471 < 5 := by
    have h11 : Real.logb 10 28471 < 5 := by
      have h12 : Real.logb 10 28471 < Real.logb 10 (100000 : ℝ) := by
        apply Real.logb_lt_logb
        all_goals norm_num
      have h13 : Real.logb 10 (100000 : ℝ) = 5 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      linarith
    linarith
  have h8 : n = 4 := by 
    by_contra h 
    push_neg at h 
    by_cases h9 : n < 4 
    · -- Assume n < 4, so n ≤ 3 
      have h10 : n ≤ 3 := by 
        omega 
      have h11 : n + 1 ≤ 4 := by 
        omega 
      have h12 : (↑(n + 1) : ℝ) ≤ (4 : ℝ) := by 
        exact_mod_cast h11 
      have h13 : (Real.logb 10 28471 : ℝ) < (4 : ℝ) := by 
        have h14 : (↑(n + 1) : ℝ) ≤ (4 : ℝ) := h12 
        nlinarith [hb_rw, h14]
      have h14 : (Real.logb 10 28471 : ℝ) < (4 : ℝ) := h13 
      nlinarith 
    · -- Assume n ≥ 4 
      have h10' : n ≥ 4 := by 
        omega 
      by_cases h9 : n > 4 
      · -- Assume n > 4, so n ≥ 5 
        have h11 : n ≥ 5 := by 
          omega 
        have h12 : a ≥ 5 := by 
          omega 
        have h13 : (a : ℝ) ≥ (5 : ℝ) := by 
          exact_mod_cast h12 
        have ha_rw : (a : ℝ) < Real.logb 10 28471 := by 
          simpa using ha 
        nlinarith 
      · -- Assume n ≤ 4 
        have h11 : n = 4 := by 
          omega 
        omega 
  have h10 : a = 4 := by 
    omega 
  have h11 : b = 5 := by 
    omega 
  omega