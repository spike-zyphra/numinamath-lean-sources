import Mathlib

theorem algebra_97946 (x : ℝ) (hx : 0 < x ∧ x ≠ 1) :
    Real.logb (2 * x) 216 = x ↔ x = 3 := by
  constructor
  · -- Forward implication: if $\log_{2x}216 = x$, then $x = 3$
    intro h
    have h1 : 0 < 2 * x := by linarith [hx.left]
    -- $2 * x \neq 1$ as $x \neq 1/2$
    have h2 : 2 * x ≠ 1 := by 
      intro h'
      have h3 : x = 1 / 2 := by linarith
      have h4 : x = 1 / 2 := h3
      have h5 : x ≠ 1 := by 
        exact hx.right
      -- Show that this gives a contradiction with our original equation
      rw [h4] at h
      -- Show that "logb 1 216 = 1 / 2" is impossible
      norm_num [Real.logb_eq_iff_rpow_eq] at h
      all_goals linarith
    -- Use the equation $Real.logb (2 * x) 216 = x$ to derive $Real.log 216 = x * Real.log (2 * x)$
    have h4 : Real.log 216 = x * Real.log (2 * x) := by 
      have h5 : Real.logb (2 * x) 216 = Real.log 216 / Real.log (2 * x) := by 
        field_simp [Real.logb]
      rw [h] at h5
      have h6 : Real.log (2 * x) ≠ 0 := by 
        by_contra h'
        have h7 : Real.log (2 * x) = 0 := by linarith
        have h8 : (2 * x) = 1 := by 
          have h9 : Real.log (2 * x) = 0 := by linarith
          have : (2 * x) = 1 := by 
            rw [Real.log_eq_zero] at h9 
            rcases h9 with (r | r | r)
            all_goals linarith 
          assumption 
        have h9 : x = 1 / 2 := by linarith
        rw [h9] at h5 
        norm_num [Real.logb_eq_iff_rpow_eq] at h5 
        all_goals linarith [hx.right]
      field_simp [h6] at h5 ⊢ 
      nlinarith 
    have ln216 : Real.log 216 = 3 * Real.log 6 := by 
      calc 
        Real.log 216 = Real.log (6^3) := by norm_num 
        _ = 3 * Real.log 6 := by simp [Real.log_pow]
    have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by 
      rw [show (6 : ℝ) = 2 * 3 by norm_num]
      rw [Real.log_mul (by linarith) (by linarith)]
    have h7 : x * (Real.log 2 + Real.log x) = 3 * (Real.log 2 + Real.log 3) := by
      have h8 : Real.log (2 * x) = Real.log 2 + Real.log x := by 
        rw [Real.log_mul (by nlinarith) (by nlinarith)]
      rw [h8] at h4
      rw [ln216] at h4
      rw [h6] at h4
      linarith 
    have h8 : x = 3 := by 
      by_cases h9 : x < 3 
      · -- Assume x < 3
        have hx2 : x < 3 := h9 
        have h10 : Real.log x < Real.log 3 := by 
          apply Real.log_lt_log 
          all_goals 
            nlinarith 
        have h11 : Real.log x < Real.log 3 := h10 
        nlinarith [sq_nonneg (Real.log x - Real.log 3), sq_nonneg (x - 3), Real.log_pos (show (2 : ℝ) > 1 by norm_num), Real.log_pos (show (3 : ℝ) > 1 by norm_num)]
      by_cases h9 : x > 3 
      · -- Assume x > 3
        have hx2 : x > 3 := h9 
        have h10 : Real.log x > Real.log 3 := by 
          apply Real.log_lt_log 
          all_goals 
            nlinarith 
        have h11 : Real.log x > Real.log 3 := h10 
        nlinarith [sq_nonneg (Real.log x - Real.log 3), sq_nonneg (x - 3), Real.log_pos (show (2 : ℝ) > 1 by norm_num), Real.log_pos (show (3 : ℝ) > 1 by norm_num)]
      -- Thus x = 3 
      linarith 
    exact h8 
  · -- Backward implication: if $x = 3$, then $\log_{2x}216 = x$
    intro h_eq
    rw [h_eq]
    have h1 : Real.logb (2 * (3 : ℝ)) 216 = 3 := by 
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
      <;> linarith 
    linarith