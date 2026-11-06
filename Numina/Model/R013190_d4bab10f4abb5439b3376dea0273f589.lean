import Mathlib

theorem algebra_7610 (a b c d : ℝ) (h : 0 ≤ a - 1 ∧ 0 ≤ b - 4 ∧ 0 ≤ c - 9 ∧ 0 ≤ d - 16)
    (h' : Real.sqrt (a - 1) + 2 * Real.sqrt (b - 4) + 3 * Real.sqrt (c - 9) + 4 * Real.sqrt (d - 16) =
    (a + b + c + d) / 2) :
    a = 2 ∧ b = 8 ∧ c = 18 ∧ d = 32 := by
  rcases h with ⟨ha1, hb4, hc9, hd16⟩
  have h1 : Real.sqrt (a - 1) ≥ 0 := by apply Real.sqrt_nonneg
  have h2 : Real.sqrt (b - 4) ≥ 0 := by apply Real.sqrt_nonneg
  have h3 : Real.sqrt (c - 9) ≥ 0 := by apply Real.sqrt_nonneg
  have h4 : Real.sqrt (d - 16) ≥ 0 := by apply Real.sqrt_nonneg
  have h1' : (Real.sqrt (a - 1)) ^ 2 = a - 1 := by
    rw [Real.sq_sqrt]
    linarith 
  have h2' : (Real.sqrt (b - 4)) ^ 2 = b - 4 := by
    rw [Real.sq_sqrt]
    linarith 
  have h3' : (Real.sqrt (c - 9)) ^ 2 = c - 9 := by
    rw [Real.sq_sqrt]
    linarith 
  have h4' : (Real.sqrt (d - 16)) ^ 2 = d - 16 := by
    rw [Real.sq_sqrt]
    linarith 
  have h6 : 
    (Real.sqrt (a - 1) - 1) ^ 2 + (Real.sqrt (b - 4) - 2) ^ 2 + (Real.sqrt (c - 9) - 3) ^ 2 + (Real.sqrt (d - 16) - 4) ^ 2 
      = 0 := by
    nlinarith [sq_nonneg (Real.sqrt (a - 1) - 1), sq_nonneg (Real.sqrt (b - 4) - 2), sq_nonneg (Real.sqrt (c - 9) - 3), sq_nonneg (Real.sqrt (d - 16) - 4), 
      Real.sqrt_nonneg (a - 1), Real.sqrt_nonneg (b - 4), Real.sqrt_nonneg (c - 9), Real.sqrt_nonneg (d - 16), 
      Real.sq_sqrt (show (0 : ℝ) ≤ a - 1 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ b - 4 by linarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ c - 9 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ d - 16 by linarith)]
  -- each is 0
  have ha2 : Real.sqrt (a - 1) - 1 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt (a - 1) - 1), sq_nonneg (Real.sqrt (b - 4) - 2), sq_nonneg (Real.sqrt (c - 9) - 3), sq_nonneg (Real.sqrt (d - 16) - 4), h6]
  have ha3 : Real.sqrt (a - 1) = 1 := by 
    linarith 
  have ha4 : a - 1 = 1 := by
    calc 
      a - 1 = (Real.sqrt (a - 1)) ^ 2 := by 
        rw [Real.sq_sqrt]
        linarith 
      _ = 1 ^ 2 := by 
        rw [ha3] 
      _ = (1 : ℝ) := by 
        norm_num 
  have ha5 : a = 2 := by 
    linarith 
  -- b
  have hb2 : Real.sqrt (b - 4) - 2 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt (a - 1) - 1), sq_nonneg (Real.sqrt (b - 4) - 2), sq_nonneg (Real.sqrt (c - 9) - 3), sq_nonneg (Real.sqrt (d - 16) - 4), h6]
  have hb3 : Real.sqrt (b - 4) = 2 := by 
    linarith 
  have hb4' : b - 4 = 4 := by
    calc 
      b - 4 = (Real.sqrt (b - 4)) ^ 2 := by 
        rw [Real.sq_sqrt]
        linarith 
      _ = 2 ^ 2 := by 
        rw [hb3] 
      _ = (4 : ℝ) := by 
        norm_num 
  have hb5 : b = 8 := by
    linarith 
  -- c
  have hc2 : Real.sqrt (c - 9) - 3 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt (a - 1) - 1), sq_nonneg (Real.sqrt (b - 4) - 2), sq_nonneg (Real.sqrt (c - 9) - 3), sq_nonneg (Real.sqrt (d - 16) - 4), h6]
  have hc3 : Real.sqrt (c - 9) = 3 := by 
    linarith 
  have hc4' : c - 9 = 9 := by
    calc 
      c - 9 = (Real.sqrt (c - 9)) ^ 2 := by 
        rw [Real.sq_sqrt]
        linarith 
      _ = 3 ^ 2 := by 
        rw [hc3] 
      _ = (9 : ℝ) := by 
        norm_num 
  have hc5 : c = 18 := by
    linarith 
  -- d
  have hd2 : Real.sqrt (d - 16) - 4 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt (a - 1) - 1), sq_nonneg (Real.sqrt (b - 4) - 2), sq_nonneg (Real.sqrt (c - 9) - 3), sq_nonneg (Real.sqrt (d - 16) - 4), h6]
  have hd3 : Real.sqrt (d - 16) = 4 := by 
    linarith 
  have hd4' : d - 16 = 16 := by
    calc 
      d - 16 = (Real.sqrt (d - 16)) ^ 2 := by 
        rw [Real.sq_sqrt]
        linarith 
      _ = 4 ^ 2 := by 
        rw [hd3] 
      _ = (16 : ℝ) := by 
        norm_num 
  have hd5 : d = 32 := by
    linarith 
  exact ⟨ha5, hb5, hc5, hd5⟩