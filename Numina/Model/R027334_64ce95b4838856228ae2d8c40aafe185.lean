import Mathlib


theorem algebra_236195 {N : ℕ} (h : (Real.sqrt 3 - 1)^N = 4817152 - 2781184 * Real.sqrt 3) :
    N = 16 := by

  have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

  have h3 : (Real.sqrt 3 - 1 : ℝ) ^ 16 = 4817152 - 2781184 * Real.sqrt 3 := by
    have h2 : (Real.sqrt 3 - 1 : ℝ) ^ 2 = 4 - 2 * Real.sqrt 3 := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), Real.sqrt_nonneg 3]
    have h5 : (Real.sqrt 3 - 1 : ℝ) ^ 4 = 28 - 16 * Real.sqrt 3 := by
      calc
        (Real.sqrt 3 - 1 : ℝ) ^ 4 = ((Real.sqrt 3 - 1 : ℝ) ^ 2) ^ 2 := by ring
        _ = (4 - 2 * Real.sqrt 3) ^ 2 := by rw [h2]
        _ = 28 - 16 * Real.sqrt 3 := by
          nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), Real.sqrt_nonneg 3]
    have h7 : (Real.sqrt 3 - 1 : ℝ) ^ 8 = 1552 - 896 * Real.sqrt 3 := by
      calc
        (Real.sqrt 3 - 1 : ℝ) ^ 8 = ((Real.sqrt 3 - 1 : ℝ) ^ 4) ^ 2 := by ring
        _ = (28 - 16 * Real.sqrt 3) ^ 2 := by rw [h5]
        _ = 1552 - 896 * Real.sqrt 3 := by
          nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), Real.sqrt_nonneg 3]
    calc
      (Real.sqrt 3 - 1 : ℝ) ^ 16 = ((Real.sqrt 3 - 1 : ℝ) ^ 8) ^ 2 := by ring
      _ = (1552 - 896 * Real.sqrt 3) ^ 2 := by rw [h7]
      _ = 4817152 - 2781184 * Real.sqrt 3 := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), Real.sqrt_nonneg 3]

  have h8 : (Real.sqrt 3 - 1 : ℝ) ^ N = (Real.sqrt 3 - 1 : ℝ) ^ 16 := by
    linarith [h, h3]

  have h9 : N = 16 := by
    have h10 : (Real.sqrt 3 - 1 : ℝ) > 0 := by
      have h100 : Real.sqrt 3 > 1 := by
        have h300 : Real.sqrt 3 > Real.sqrt 1 := by
          apply Real.sqrt_lt_sqrt
          all_goals norm_num
        have h301 : Real.sqrt 1 = (1 : ℝ) := by
          rw [Real.sqrt_one]
        nlinarith [h300, h301, Real.sqrt_nonneg 3, Real.sqrt_nonneg 1]
      nlinarith

    have h100 : (N : ℝ) = (16 : ℝ) := by
      have h14 : (Real.sqrt 3 - 1 : ℝ) ^ (N : ℝ) = (Real.sqrt 3 - 1 : ℝ) ^ (16 : ℝ) := by
        exact_mod_cast h8
      have h101 : (N : ℝ) = (16 : ℝ) := by
        apply_fun (Real.logb (Real.sqrt 3 - 1)) at h14
        have h102 : Real.logb (Real.sqrt 3 - 1) ((Real.sqrt 3 - 1 : ℝ) ^ (N : ℝ)) = Real.logb (Real.sqrt 3 - 1) ((Real.sqrt 3 - 1 : ℝ) ^ (16 : ℝ)) := by linarith [h14]
        have h103 : Real.logb (Real.sqrt 3 - 1) ((Real.sqrt 3 - 1 : ℝ) ^ (N : ℝ)) = (N : ℝ) := by
          rw [Real.logb_rpow]
          all_goals
            try { nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), Real.sqrt_nonneg 3] }
        have h104 : Real.logb (Real.sqrt 3 - 1) ((Real.sqrt 3 - 1 : ℝ) ^ (16 : ℝ)) = (16 : ℝ) := by
          rw [Real.logb_rpow]
          all_goals
            try { nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), Real.sqrt_nonneg 3] }
        linarith [h103, h104, h102]
      linarith

    have h12 : N = 16 := by
      exact_mod_cast h100
    exact h12

  exact h9