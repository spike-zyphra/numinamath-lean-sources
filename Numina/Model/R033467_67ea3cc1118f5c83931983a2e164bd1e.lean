import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_228483 {f : ℝ → ℝ}
  (hf : f = λ x => logb 2 (18 * 4^x - 8 * 2^x + 1) - 2 * x - 1) :
  f (-2) = 0 ∧ ∀ x, f x = 0 → x = -2 := by
  have h1 : f (-2) = 0 := by
    rw [hf]
    have h2 : (18 * (4:ℝ)^(-2:ℝ) - 8 * (2:ℝ)^(-2:ℝ) + 1) = (1:ℝ)/8 := by
      norm_num
    have h3 : logb 2 (18 * (4:ℝ)^(-2:ℝ) - 8 * (2:ℝ)^(-2:ℝ) + 1) = -3 := by
      rw [h2]
      have h4 : logb (2:ℝ) (1/8) = logb (2:ℝ) ( (2:ℝ)^(-3:ℝ) ) := by
        norm_num
      rw [h4]
      rw [logb_rpow]
      all_goals norm_num
    simp only [h3]
    norm_num
  have h2 : ∀ x, f x = 0 → x = -2 := by
    intro x hx
    rw [hf] at hx
    have h_eq : logb 2 (18 * (4:ℝ)^x - 8 * (2:ℝ)^x + 1) - 2 * x - 1 = 0 := by
      simpa using hx
    have h3 : (18 * (4:ℝ)^x - 8 * (2:ℝ)^x + 1) = (18 * ((2:ℝ)^x)^2 - 8 * ((2:ℝ)^x) + 1) := by
      have h4 : (4:ℝ)^x = ((2:ℝ)^x)^2 := by
        have h5 : ((2:ℝ)^x)^2 = (2:ℝ)^(2 * x) := by 
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          ring_nf
          all_goals linarith
        have h6 : (4:ℝ)^x = (2:ℝ)^(2 * x) := by
          rw [show (4:ℝ) = (2:ℝ) ^ (2:ℝ) by norm_num]
          rw [← Real.rpow_mul]
          ring_nf
          all_goals linarith
        rw [h6, h5]
      rw [h4]
    have h_eq' : logb 2 (18 * ((2: ℝ)^x)^2 - 8 * ((2: ℝ)^x) + 1) = 2 * x + 1 := by
      have h4 : logb 2 (18 * (4:ℝ)^x - 8 * (2:ℝ)^x + 1) = 2 * x + 1 := by
        linarith [h_eq]
      rw [h3] at h4
      linarith [h4]
    have eq5 : (18 * ((2: ℝ)^x)^2 - 8 * ((2: ℝ)^x) + 1) = (2: ℝ)^(2 * x + 1) := by
      have eq6 : (18 * ((2: ℝ)^x)^2 - 8 * ((2: ℝ)^x) + 1) > 0 := by
        nlinarith [sq_nonneg ((2: ℝ) ^x - (1: ℝ) / 4), Real.rpow_pos_of_pos (show (2: ℝ) > 0 by norm_num) x, Real.rpow_nonneg (show (0: ℝ) ≤ (2: ℝ) by norm_num) (2 * x + 1)]
      rw [logb_eq_iff_rpow_eq] at h_eq'
      · -- Show that (18 * ((2: ℝ) ^x)^2 - 8 * ((2: ℝ) ^x) + 1) = (2 : ℝ)^(2 * x + 1)
        linarith [h_eq']
      all_goals
        try linarith [Real.rpow_pos_of_pos (show (0: ℝ) < 2 by norm_num) x, Real.rpow_pos_of_pos (show (0: ℝ) < 2 by norm_num) (2 * x + 1)]
        all_goals nlinarith
    -- Now manipulating our exponential equation
    -- to get to our quadratic
    -- The error was in my previous approach
    -- Let's fix in the new approach
    have h6 : 16 * ((2: ℝ)^x)^2 - 8 * ((2: ℝ)^x) + 1 = 0 := by
      have eq7 : (18 * ((2: ℝ)^x)^2 - 8 * ((2: ℝ)^x) + 1) = (2: ℝ)^(2 * x + 1) := eq5
      have eq8 : (2: ℝ)^(2 * x + 1) = 2 * ((2: ℝ)^x)^2 := by
        have eq9 : (2: ℝ)^(2 * x + 1) = 2 * ((2: ℝ)^x)^2 := by
          have eq10 : (2: ℝ)^(2 * x + 1) = (2: ℝ)^(2 * x) * (2: ℝ)^(1: ℝ) := by
            rw [show 2 * x + 1 = (2 * x) + (1: ℝ) by ring]
            rw [Real.rpow_add]
            all_goals norm_num
          rw [eq10]
          have eq11 : (2: ℝ)^(2 * x) = ((2: ℝ)^x)^2 := by
            have eq12 : (2: ℝ)^(2 * x) = ((2: ℝ)^x)^2 := by
              calc 
                (2: ℝ)^(2 * x) = (2: ℝ)^(2 * x) := by rfl
                _ = ((2: ℝ)^x)^2 := by 
                  rw [← Real.rpow_natCast, ← Real.rpow_mul]
                  ring_nf
                  all_goals linarith
            linarith [eq12]
          rw [eq11]
          <;> ring_nf <;> norm_num
        linarith [eq9]
      rw [eq8] at eq7
      nlinarith
    have h7 : (4 * (2: ℝ) ^x - 1)^2 = 0 := by
      nlinarith [h6]
    have h8 : 4 * (2: ℝ) ^x - 1 = 0 := by
      nlinarith [pow_nonneg (show 0 ≤ 4 * (2: ℝ) ^x -1 by nlinarith) 2, sq_nonneg (4 * (2: ℝ) ^x -1), Real.rpow_pos_of_pos (show (0: ℝ) < 2 by norm_num) x]
    have h9 : (2: ℝ) ^x > 0 := by positivity
    have h10 : (2: ℝ) ^x = (1: ℝ) / 4 := by
      nlinarith
    have h11 : x = -2 := by 
      have h12 : x = Real.logb (2: ℝ) ((2: ℝ) ^x) := by 
        rw [Real.logb_rpow]
        all_goals norm_num
      rw [h12, h10]
      have h13 : Real.logb (2: ℝ) (1 / 4) = -2 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      linarith [h13]
    exact h11
  constructor
  · exact h1
  · exact h2