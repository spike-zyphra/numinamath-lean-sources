import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_171130 (x : ℝ) (hx : 0 < x ∧ x ≠ 1) :
    logb 5 (sqrt (3 * x + 4)) * logb x 5 > 1 ↔ x ∈ Ioo 1 4 := by
  constructor
  · -- Assume the inequality holds
    intro h
    have hx1 : 0 < x := hx.1
    have hx2 : x ≠ 1 := hx.2
    have h1 : sqrt (3 * x + 4) > 0 := by
      have h2 : 3 * x + 4 > 0 := by
        nlinarith
      have h3 : sqrt (3 * x + 4) > 0 := by
        positivity
      exact h3
    have h2 : logb 5 (sqrt (3 * x + 4)) = (1 / 2) * logb 5 (3 * x + 4) := by
      have h4 : 0 < 3 * x + 4 := by 
        nlinarith
      have h11 : sqrt (3 * x + 4) = (3 * x + 4) ^ (1 / 2 : ℝ) := by 
        rw [Real.sqrt_eq_rpow]
      rw [h11]
      rw [logb_rpow_eq_mul_logb_of_pos]
      all_goals
        nlinarith
    have h3 : logb x 5 = 1 / (logb 5 x) := by 
      field_simp [logb]
    rw [h2, h3] at h
    have h4 : x > 1 := by
      by_contra h4
      push_neg at h4
      have h5 : x < 1 := by
        by_contra h7
        push_neg at h7
        have h30 : x ≥ 1 := by
          nlinarith
        have h40 : x = 1 := by
          nlinarith [h30, show x ≤ 1 by nlinarith]
        tauto
      have h6 : logb 5 x < 0 := by
        have h7 : x < 1 := h5
        have h8 : logb 5 x < 0 := by 
          have h9 : logb 5 x = Real.log x / Real.log (5 : ℝ) := by
            field_simp [logb]
          rw [h9]
          have h20 : Real.log (5 : ℝ) > 0 := by
            apply Real.log_pos
            all_goals
              norm_num
          have h10 : Real.log x < 0 := by
            have h11 : x < 1 := h5
            have h12 : Real.log x < Real.log (1 : ℝ) := by
              apply Real.log_lt_log
              all_goals
                nlinarith
            have h13 : Real.log (1 : ℝ) = 0 := by
              rw [Real.log_one]
            linarith
          apply div_neg_of_neg_of_pos
          all_goals linarith
        linarith
      have h13 : logb 5 (3 * x + 4) > 0 := by
        have h14 : 3 * x + 4 > 1 := by
          nlinarith
        have h15 : logb 5 (3 * x + 4) > 0 := by
          have h16 : logb 5 (3 * x + 4) > logb 5 (1 : ℝ) := by
            apply Real.logb_lt_logb
            all_goals
              try { norm_num }
              all_goals
                nlinarith
          have h17 : logb 5 (1 : ℝ) = 0 := by
            simp [logb_one]
          linarith
        linarith
      have h14 : (1 / 2) * logb 5 (3 * x + 4) * (1 / (logb 5 x)) < 0 := by
        have h15 : logb 5 x < 0 := h6
        have h130 : (1 / (logb 5 x)) < 0 := by
          apply div_neg_of_pos_of_neg
          norm_num
          all_goals linarith
        have h120 : (1 / 2) * logb 5 (3 * x + 4) > 0 := by
          apply mul_pos
          all_goals
            positivity
          all_goals linarith
        nlinarith
      nlinarith
    have h5 : logb 5 x > 0 := by
      apply Real.logb_pos
      all_goals
      try { norm_num  }
      all_goals
      try {  nlinarith  }
    have h6 : (1 / 2) * logb 5 (3 * x + 4) * (1 / (logb 5 x)) > 1 := by
      linarith
    have h7 : logb 5 (3 * x + 4) > 2 * logb 5 x := by
      have h8 : (1 / 2) * logb 5 (3 * x + 4) / (logb 5 x) > 1 := by
        have h0 : (1 / 2) * logb 5 (3 * x + 4) * (1 / (logb 5 x)) > 1 := h6
        have h9 : logb 5 x > 0 := h5
        have h10 : (1 / 2) * logb 5 (3 * x + 4) / (logb 5 x) = (1 / 2) * logb 5 (3 * x + 4) * (1 / (logb 5 x)) := by
          field_simp
        linarith [h10, h6]
      have h9 : logb 5 x > 0 := h5
      apply (lt_div_iff₀ (by nlinarith)).mp at h8
      nlinarith
    have h11 : (3 * x + 4) > (x) ^ 2 := by
      have h12 : logb 5 (3 * x + 4) > 2 * logb 5 x := h7
      have h13 : 2 * logb 5 x = logb 5 (x ^ 2) := by
        simp [logb_pow]
      rw [h13] at h12
      have h100 : (3 * x + 4 : ℝ) > (x ^ 2 : ℝ) := by
        apply (Real.logb_lt_logb_iff (by norm_num) (by nlinarith) (by nlinarith)).mp at h12
        nlinarith
      nlinarith
    have h13 : x < 4 := by 
      nlinarith [sq_nonneg (x - 4 : ℝ), sq_nonneg (x + 1 : ℝ)]
    exact ⟨by nlinarith, by nlinarith⟩
  · -- Assume x ∈ Ioo 1 4
    rintro ⟨hx1, hx2⟩
    have hx0 : 0 < x := by linarith
    have hx12 : x ≠ 1 := by 
      nlinarith
    have h1 : sqrt (3 * x + 4) > 0 := by
      have h2 : 3 * x + 4 > 0 := by
        nlinarith
      have h3 : sqrt (3 * x + 4) > 0 := by
        positivity
      exact h3
    have h2 : logb 5 (sqrt (3 * x + 4)) = (1 / 2) * logb 5 (3 * x + 4) := by
      have h4 : 0 < 3 * x + 4 := by 
        nlinarith
      have h11 : sqrt (3 * x + 4) = (3 * x + 4) ^ (1 / 2 : ℝ) := by 
        rw [Real.sqrt_eq_rpow]
      rw [h11]
      rw [logb_rpow_eq_mul_logb_of_pos]
      all_goals
        nlinarith
    have h3 : logb x 5 = 1 / (logb 5 x) := by 
      field_simp [logb]
    rw [h2, h3]
    have h4 : x > 1 := by linarith
    have h5 : logb 5 x > 0 := by
      apply Real.logb_pos
      all_goals
      try { norm_num  }
      all_goals
      try {  nlinarith  }
    have h6 : (1 / 2) * logb 5 (3 * x + 4) * (1 / (logb 5 x) ) > 1 := by
      have h7 : logb 5 (3 * x + 4) > 2 * logb 5 x := by 
        have h11 : (3 * x + 4) > (x) ^ 2 := by 
          nlinarith [sq_nonneg (x - 4 : ℝ), sq_nonneg (x + 1 : ℝ)]
        have h10 : logb 5 (3 * x + 4) > logb 5 (x ^ 2) := by 
          apply Real.logb_lt_logb
          all_goals
          try { norm_num  }
          all_goals
          nlinarith
        have h13 : logb 5 (x ^ 2) = 2 * logb 5 x := by 
          simp [logb_pow]
        nlinarith
      have h9 : (1 / 2) * logb 5 (3 * x + 4) > (1 : ℝ) * (logb 5 x) := by 
        nlinarith
      have h10 : (1 / 2) * logb 5 (3 * x + 4) * (1 / (logb 5 x) ) > 1 := by
        have h110 : (1 / (logb 5 x) ) > 0 := by
          positivity
        have h120 : (1 / 2) * logb 5 (3 * x + 4) > (1 * (logb 5 x) ) := by
          nlinarith
        have h130 : (1 / 2) * logb 5 (3 * x + 4) * (1 / (logb 5 x) ) > (1 * (logb 5 x) ) * (1 / (logb 5 x) ) := by
          have h140 : (1 / (logb 5 x) ) > 0 := by
            positivity
          nlinarith [show (1 * (logb 5 x) ) < (1 / 2) * logb 5 (3 * x + 4) by 
            nlinarith
          ]
        have h60 : (1 * (logb 5 x) ) * (1 / (logb 5 x) ) = 1 := by
          field_simp
        nlinarith
      linarith
    linarith