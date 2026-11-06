import Mathlib
set_option maxHeartbeats 50000000

open Real Set
open scoped BigOperators

theorem algebra_165699 {x : ℝ} (hx : x > 0) :
  logb 5 (3^x + 4^x) = logb 4 (5^x - 3^x) ↔ x = 2 := by
  constructor
  · -- Assume logb 5 (3^x + 4^x) = logb 4 (5^x - 3^x), prove x = 2
    intro h
    set y := logb 5 (3^x + 4^x)
    have h1 : (3 : ℝ) ^ x + (4 : ℝ) ^ x = (5 : ℝ) ^ y := by
      refine Eq.symm (rpow_logb ?_ ?_ ?_)
      norm_num
      norm_num
      positivity

    -- From h, we also know that y = log_4 (5^x - 3^x).
    have h2 : y = logb 4 (5^x - 3^x) := h
    have h2' : (5 : ℝ) ^ x - (3 : ℝ) ^ x = (4 : ℝ) ^ y := by 
      rw [h2]
      refine Eq.symm (rpow_logb ?_ ?_ ?_)
      norm_num
      norm_num
      have h51 : (5 : ℝ) ^ x > (3 : ℝ) ^ x := by
        apply Real.rpow_lt_rpow 
        all_goals
          linarith
      have h52 : (5 : ℝ) ^ x - (3 : ℝ) ^ x > 0 := by linarith
      linarith

    -- Since x and y must be equal for the equations to hold, we use the derived fact that x = 2 to get the answer.
    have eq3 : x = y := by
      have eq1 : (3 : ℝ) ^x + (4 : ℝ)^x = (5 : ℝ) ^ y := h1
      have eq2 : (5 : ℝ) ^x - (3 : ℝ)^x = (4 : ℝ) ^ y := h2'
      have eq3 : (4 : ℝ) ^x + (5 : ℝ)^x = (4 : ℝ) ^ y + (5 : ℝ)^ y := by
        linarith
      by_cases h_eq : x < y
      · -- Assume x < y
        have h41 : (4 : ℝ) ^ x < (4 : ℝ) ^ y := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals
            linarith
        have h51 : (5 : ℝ) ^ x < (5 : ℝ) ^ y := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals
            linarith
        have h61 : (4 : ℝ) ^x + (5 : ℝ)^x < (4 : ℝ) ^ y + (5 : ℝ) ^ y := by
          linarith
        linarith [ h61, eq3 ]
      by_cases h_eq1 : y < x
      · -- Assume y < x
        have h41 : (4 : ℝ) ^ y < (4 : ℝ) ^ x := by 
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals
            linarith
        have h51 : (5 : ℝ) ^ y < (5 : ℝ) ^ x := by 
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals
            linarith
        have h61 : (4 : ℝ) ^ y + (5 : ℝ) ^ y < (4 : ℝ) ^x + (5 : ℝ) ^x := by
          linarith
        linarith [ h61, eq3 ]
      linarith

    -- Now using y = x, we can compute that x must be 2.
    have h4 : (3 : ℝ) ^x + (4 : ℝ)^x = (5 : ℝ) ^x := by
      rw [ show y = x by linarith [ eq3] ] at h1
      exact h1
    have eq2 : x = 2 := by
      have eq1 : (3 : ℝ) ^x + (4 : ℝ) ^x = (5 : ℝ) ^x := h4 
      have eq3 : ((3 : ℝ) / (5 : ℝ)) ^ x + ((4 : ℝ) / (5 : ℝ)) ^ x = 1 := by
        have eq4 : ((3 : ℝ) / (5 : ℝ)) ^ x = ((3 : ℝ) ^ x) / ((5 : ℝ) ^ x) := by
          rw [← Real.div_rpow]
          all_goals linarith
        have eq5 : ((4 : ℝ) / (5 : ℝ)) ^ x = ((4 : ℝ) ^ x) / ((5 : ℝ) ^ x) := by 
          rw [← Real.div_rpow]
          all_goals linarith
        rw [eq4, eq5]
        have eq6 : ((3 : ℝ) ^x + (4 : ℝ) ^x) / ((5 : ℝ) ^x) = 1 := by
          have eq7 : (3 : ℝ) ^x + (4 : ℝ) ^x = (5 : ℝ) ^x := h4
          field_simp [ show (5 : ℝ) ^x > 0 by positivity ]
          linarith
        have eq7 : ((3 : ℝ) ^x / ((5 : ℝ) ^x) ) + ( (4 : ℝ) ^x / ((5 : ℝ) ^x) ) = ((3 : ℝ) ^x + (4 : ℝ) ^x) / ((5 : ℝ) ^x) := by
          field_simp [ show (5 : ℝ) ^x > 0 by positivity ]
        linarith [eq6, eq7]
      have eq4 : x = 2 := by
        by_cases h8 : x < (2 : ℝ)
        · -- Case: x < 2
          have h9 : ((3 : ℝ) / (5 : ℝ)) ^x + ((4 : ℝ) / (5 : ℝ)) ^ x > 1 := by
            have h10 : x < (2 : ℝ) := h8 
            have h11 : ((3 : ℝ) / (5 : ℝ)) ^x > ((3 : ℝ) / (5 : ℝ)) ^ (2 : ℝ) := by 
              apply Real.rpow_lt_rpow_of_exponent_gt 
              all_goals linarith
            have h12 : ((4 : ℝ) / (5 : ℝ)) ^x > ((4 : ℝ) / (5 : ℝ)) ^ (2 : ℝ) := by 
              apply Real.rpow_lt_rpow_of_exponent_gt 
              all_goals
                linarith
            have h13 : ((3 : ℝ) / (5 : ℝ)) ^ (2 : ℝ) = 9 / 25 := by
              norm_num [Real.rpow_natCast, pow_two]
            have h14 : ((4 : ℝ) / (5 : ℝ)) ^ (2 : ℝ) = 16 / 25 := by
              norm_num [Real.rpow_natCast, pow_two]
            have h15 : ((3 : ℝ) / (5 : ℝ)) ^ (2 : ℝ) + ((4 : ℝ) / (5 : ℝ)) ^ (2 : ℝ) = 1 := by
              rw [ h13, h14 ]
              norm_num 
            nlinarith
          linarith [eq3, h9]
        by_cases h8 : x > (2 : ℝ)
        · -- Case: x > 2
          have h9 : ((3 : ℝ) / (5 : ℝ)) ^x + ((4 : ℝ) / (5 : ℝ)) ^x < 1 := by
            have h11 : ((3 : ℝ) / (5 : ℝ)) ^x < ((3 : ℝ) / (5 : ℝ)) ^ (2 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_gt 
              all_goals
                linarith
            have h12 : ((4 : ℝ) / (5 : ℝ)) ^x < ((4 : ℝ) / (5 : ℝ)) ^ (2 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_gt 
              all_goals
                linarith
            have h13 : ((3 : ℝ) / (5 : ℝ)) ^ (2 : ℝ) = 9 / 25 := by
                norm_num [Real.rpow_natCast, pow_two]
            have h14 : ((4 : ℝ) / (5 : ℝ)) ^ (2 : ℝ) = 16 / 25 := by
                norm_num [Real.rpow_natCast, pow_two]
            have h15 : ((3 : ℝ) / (5 : ℝ)) ^ (2 : ℝ) + ((4 : ℝ) / (5 : ℝ)) ^ (2 : ℝ) = 1 := by
                rw [ h13, h14 ]
                norm_num 
            nlinarith
          linarith [eq3, h9]
        linarith
      exact eq4 
    exact eq2 
  · -- Assume x = 2, prove logb 5 (3^x + 4^x) = logb 4 (5^x - 3^x)
    intro h2
    rw [h2]
    have h_eq1 : (3 : ℝ) ^ (2 : ℝ) + (4 : ℝ) ^ (2 : ℝ) = (5 : ℝ) ^ (2 : ℝ) := by
      norm_num [Real.rpow_natCast, pow_two]
    have h_eq2 : (5 : ℝ) ^ (2 : ℝ) - (3 : ℝ) ^ (2 : ℝ) = (4 : ℝ) ^ (2 : ℝ) := by 
      norm_num [Real.rpow_natCast, pow_two]

    have h_eq3 : logb (5 : ℝ) ((3 : ℝ) ^ (2 : ℝ) + (4 : ℝ) ^ (2 : ℝ)) = logb (5 : ℝ) ((5 : ℝ) ^ (2 : ℝ)) := by
      rw [show (3 : ℝ) ^ (2 : ℝ) + (4 : ℝ) ^ (2 : ℝ) = (5 : ℝ) ^ (2 : ℝ) by linarith [h_eq1]]

    have h_eq4 : logb (4 : ℝ) ((5 : ℝ) ^ (2 : ℝ) - (3 : ℝ) ^ (2 : ℝ)) = logb (4 : ℝ) ((4 : ℝ) ^ (2 : ℝ)) := by 
      rw [show (5 : ℝ) ^ (2 : ℝ) - (3 : ℝ) ^ (2 : ℝ) = (4 : ℝ) ^ (2 : ℝ) by linarith [h_eq2]]

    rw [h_eq3, h_eq4]

    have h_eq5 : logb (5 : ℝ) ((5 : ℝ) ^ (2 : ℝ)) = (2 : ℝ) := by 
      rw [logb_rpow]
      all_goals norm_num
    have h_eq6 : logb (4 : ℝ) ((4 : ℝ) ^ (2 : ℝ)) = (2 : ℝ) := by 
      rw [logb_rpow]
      all_goals norm_num
    rw [h_eq5, h_eq6]
    all_goals norm_num