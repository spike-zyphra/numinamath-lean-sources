import Mathlib

open Real

theorem algebra_98445 {n : ℕ} (hn : n = 31) :
    5 = ∏ i ∈ Finset.Icc 2 n, logb i (i + 1) := by
  rw [hn]
  have h1 : ∏ i in Finset.Icc (2 : ℕ) (31 : ℕ), logb i (i + 1) = (5 : ℝ) := by
    have h2 : ∏ i in Finset.Icc (2 : ℕ) (31 : ℕ), logb i (i + 1) =
      logb 2 3 * logb 3 4 * logb 4 5 * logb 5 6 * logb 6 7 * logb 7 8 * logb 8 9 * logb 9 10 * logb 10 11 * logb 11 12 * logb 12 13 * logb 13 14 * logb 14 15 * logb 15 16 * logb 16 17 * logb 17 18 * logb 18 19 * logb 19 20 * logb 20 21 * logb 21 22 * logb 22 23 * logb 23 24 * logb 24 25 * logb 25 26 * logb 26 27 * logb 27 28 * logb 28 29 * logb 29 30 * logb 30 31 * logb 31 32 := by
      norm_num [Finset.prod_Icc_succ_top]
    rw [h2]
    have h3 : logb 2 3 * logb 3 4 * logb 4 5 * logb 5 6 * logb 6 7 * logb 7 8 * logb 8 9 * logb 9 10 * logb 10 11 * logb 11 12 * logb 12 13 * logb 13 14 * logb 14 15 * logb 15 16 * logb 16 17 * logb 17 18 * logb 18 19 * logb 19 20 * logb 20 21 * logb 21 22 * logb 22 23 * logb 23 24 * logb 24 25 * logb 25 26 * logb 26 27 * logb 27 28 * logb 28 29 * logb 29 30 * logb 30 31 * logb 31 32 = (5 : ℝ) := by
      have h4 : logb 2 3 * logb 3 4 * logb 4 5 * logb 5 6 * logb 6 7 * logb 7 8 * logb 8 9 * logb 9 10 * logb 10 11 * logb 11 12 * logb 12 13 * logb 13 14 * logb 14 15 * logb 15 16 * logb 16 17 * logb 17 18 * logb 18 19 * logb 19 20 * logb 20 21 * logb 21 22 * logb 22 23 * logb 23 24 * logb 24 25 * logb 25 26 * logb 26 27 * logb 27 28 * logb 28 29 * logb 29 30 * logb 30 31 * logb 31 32 =
          Real.log 32 / Real.log 2 := by
        have h5 : logb 2 3 = Real.log 3 / Real.log 2 := by
          field_simp [logb]
        have h6 : logb 3 4 = Real.log 4 / Real.log 3 := by
          field_simp [logb]
        have h7 : logb 4 5 = Real.log 5 / Real.log 4 := by
          field_simp [logb]
        have h8 : logb 5 6 = Real.log 6 / Real.log 5 := by
          field_simp [logb]
        have h9 : logb 6 7 = Real.log 7 / Real.log 6 := by
          field_simp [logb]
        have h10 : logb 7 8 = Real.log 8 / Real.log 7 := by
          field_simp [logb]
        have h11 : logb 8 9 = Real.log 9 / Real.log 8 := by
          field_simp [logb]
        have h12 : logb 9 10 = Real.log 10 / Real.log 9 := by
          field_simp [logb]
        have h13 : logb 10 11 = Real.log 11 / Real.log 10 := by
          field_simp [logb]
        have h14 : logb 11 12 = Real.log 12 / Real.log 11 := by
          field_simp [logb]
        have h15 : logb 12 13 = Real.log 13 / Real.log 12 := by
          field_simp [logb]
        have h16 : logb 13 14 = Real.log 14 / Real.log 13 := by
          field_simp [logb]
        have h17 : logb 14 15 = Real.log 15 / Real.log 14 := by
          field_simp [logb]
        have h18 : logb 15 16 = Real.log 16 / Real.log 15 := by
          field_simp [logb]
        have h19 : logb 16 17 = Real.log 17 / Real.log 16 := by
          field_simp [logb]
        have h20 : logb 17 18 = Real.log 18 / Real.log 17 := by
          field_simp [logb]
        have h21 : logb 18 19 = Real.log 19 / Real.log 18 := by
          field_simp [logb]
        have h22 : logb 19 20 = Real.log 20 / Real.log 19 := by
          field_simp [logb]
        have h23 : logb 20 21 = Real.log 21 / Real.log 20 := by
          field_simp [logb]
        have h24 : logb 21 22 = Real.log 22 / Real.log 21 := by
          field_simp [logb]
        have h25 : logb 22 23 = Real.log 23 / Real.log 22 := by
          field_simp [logb]
        have h26 : logb 23 24 = Real.log 24 / Real.log 23 := by
          field_simp [logb]
        have h27 : logb 24 25 = Real.log 25 / Real.log 24 := by
          field_simp [logb]
        have h28 : logb 25 26 = Real.log 26 / Real.log 25 := by
          field_simp [logb]
        have h29 : logb 26 27 = Real.log 27 / Real.log 26 := by
          field_simp [logb]
        have h30 : logb 27 28 = Real.log 28 / Real.log 27 := by
          field_simp [logb]
        have h31 : logb 28 29 = Real.log 29 / Real.log 28 := by
          field_simp [logb]
        have h32 : logb 29 30 = Real.log 30 / Real.log 29 := by
          field_simp [logb]
        have h33 : logb 30 31 = Real.log 31 / Real.log 30 := by
          field_simp [logb]
        have h34 : logb 31 32 = Real.log 32 / Real.log 31 := by
          field_simp [logb]
        rw [h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
        have h35 : Real.log 32 = 5 * Real.log 2 := by
          calc
            Real.log 32 = Real.log (2 ^ 5) := by norm_num
            _ = 5 * Real.log 2 := by simp [Real.log_pow]
        field_simp [h35]
        <;> ring
      rw [h4]
      have h35 : Real.log 32 = 5 * Real.log 2 := by
        calc
          Real.log 32 = Real.log (2 ^ 5) := by norm_num
          _ = 5 * Real.log 2 := by simp [Real.log_pow]
      rw [h35]
      field_simp
    linarith
  linarith