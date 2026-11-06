import Mathlib
set_option maxHeartbeats 400000

open Real

theorem algebra_153900 {x : ℝ} (hx : (x : ℝ) > ( 3 : ℝ)) :
    logb 19 (x - 3) + logb 93 (x - 3) = 3 - logb 10 (x ^ 5 - 24) ↔ x = 4 := by
  constructor
  · -- Forward: if the equation holds, then $x = 4$.
    intro h 
    have h51: (x - 3 : ℝ) > 0 := by linarith 
    have h52: (x ^ 5 - 24 : ℝ) > 0 := by
      have h11: x > (3 : ℝ) := hx
      have h22: x^5 > (3 : ℝ) ^ 5 := by
        apply pow_lt_pow_left
        all_goals linarith
      have h341: (3 : ℝ) ^ 5 = 243 := by norm_num 
      have h342: (243 : ℝ) < x ^ 5 := by linarith [h22, h341]
      nlinarith
    have h50: logb 19 (x - 3) + logb 93 (x - 3) = 3 - logb 10 (x ^ 5 - 24) := h
    by_cases h10 : x > 4 
    · -- If x > 4 
      have h30: x > 4 := h10 
      have h31 : (x - 3 : ℝ) > (4 - 3 : ℝ) := by linarith 
      have h32 : (x : ℝ) ^ 5 > (4 : ℝ) ^ 5 := by
        apply pow_lt_pow_left 
        all_goals linarith 
      have h33 : (x ^ 5 - 24 : ℝ) > (4 ^ 5 - 24 : ℝ) := by
        nlinarith 
      have h11 : logb (19 : ℝ) (x - 3 : ℝ) > logb (19 : ℝ) (4 - 3 : ℝ) := by
        apply Real.logb_lt_logb 
        all_goals norm_num  -- Use norm_num to handle numeric goals
        all_goals nlinarith -- For positivity goals that norm_num didn't complete
      have h12 : logb (93 : ℝ) (x - 3 : ℝ) > logb (93 : ℝ) (4 - 3 : ℝ) := by 
        apply Real.logb_lt_logb 
        all_goals norm_num 
        all_goals nlinarith 
      have h13 : logb (10 : ℝ) (x ^ 5 - 24 : ℝ) > logb (10 : ℝ) (4 ^ 5 - 24 : ℝ) := by 
        apply Real.logb_lt_logb 
        all_goals norm_num 
        all_goals nlinarith 
      have h700 : logb 19 (4 - 3 : ℝ) = 0 := by
        have h701 : (4 - 3 : ℝ) = (1 : ℝ) := by norm_num  -- First simplify 4 - 3
        rw [h701]  -- Rewrite with this equality
        simp  -- Now simp can prove logb 19 1 = 0
      have h702 : logb 93 (4 - 3 : ℝ) = 0 := by
        have h703 : (4 - 3 : ℝ) = (1 : ℝ) := by norm_num 
        rw [h703]
        simp 
      have h704 : logb 19 (x - 3) + logb 93 (x - 3) > (0 : ℝ) := by 
        nlinarith [h11, h12, h700, h702]
      have h740 : logb 10 (4 ^ 5 - 24 : ℝ) = 3 := by 
        have h11811 : (4 ^ 5 - 24 : ℝ) = (1000 : ℝ) := by norm_num 
        rw [h11811]
        have h100 : logb (10 : ℝ) (1000 : ℝ) = 3 := by 
          have h222 : (1000 : ℝ) = 10 ^ 3 := by norm_num 
          rw [h222] 
          simp [logb_pow]
        exact h100 
      have h741 : 3 - logb 10 (x ^ 5 - 24 : ℝ) < (0 : ℝ) := by 
        nlinarith [h13, h740]
      linarith 
    by_cases h7 : x < 4
    · -- If x < 4
      have h60 : x < 4 := h7 
      have h57 : (x - 3 : ℝ) < (4 - 3 : ℝ) := by linarith 
      have h59 : (x : ℝ) ^ 5 < (4 : ℝ) ^ 5 := by 
        apply pow_lt_pow_left 
        all_goals linarith 
      have h58 : (x ^ 5 - 24 : ℝ) < (4 ^ 5 - 24 : ℝ) := by 
        nlinarith 
      have h70 : logb (19 : ℝ) (x - 3 : ℝ) < logb (19 : ℝ) (4 - 3 : ℝ) := by 
        apply Real.logb_lt_logb 
        all_goals norm_num 
        all_goals nlinarith 
      have h71 : logb (93 : ℝ) (x - 3 : ℝ) < logb (93 : ℝ) (4 - 3 : ℝ) := by
        apply Real.logb_lt_logb 
        all_goals norm_num 
        all_goals nlinarith 
      have h72 : logb (10 : ℝ) (x ^ 5 - 24 : ℝ) < logb (10 : ℝ) (4 ^ 5 - 24 : ℝ) := by 
        apply Real.logb_lt_logb 
        all_goals norm_num 
        all_goals nlinarith 
      have h700 : logb 19 (4 - 3 : ℝ) = 0 := by
        have h701 : (4 - 3 : ℝ) = (1 : ℝ) := by norm_num 
        rw [h701]
        simp 
      have h702 : logb 93 (4 - 3 : ℝ) = 0 := by 
        have h703 : (4 - 3 : ℝ) = 1 := by norm_num 
        rw [h703] 
        simp 
      have h740 : logb 10 (4 ^ 5 - 24 : ℝ) = 3 := by 
        have h11811 : (4 ^ 5 - 24 : ℝ) = (1000 : ℝ) := by norm_num 
        rw [h11811] 
        have h100 : logb (10 : ℝ) (1000 : ℝ) = 3 := by 
          have h222 : (1000 : ℝ) = 10 ^ 3 := by norm_num 
          rw [h222] 
          simp [logb_pow]
        exact h100 
      have h74 : logb 19 (x - 3) + logb 93 (x - 3) < (0 : ℝ) := by 
        linarith [h70, h71, h700, h702]
      have h75 : (3 : ℝ) - logb 10 (x ^ 5 - 24) > (0 : ℝ) := by
        linarith [h72, h740]
      linarith 
    linarith 
  · -- Backward: If x = 4, then the equation holds.
    intro h 
    rw [h]
    have h1 : logb 19 (4 - 3 : ℝ) = 0 := by 
      have h701 : (4 - 3 : ℝ) = (1 : ℝ) := by norm_num 
      rw [h701] 
      simp 
    have h2 : logb 93 (4 - 3 : ℝ) = 0 := by 
      have h701 : (4 - 3 : ℝ) = 1 := by norm_num 
      rw [h701] 
      simp 
    have h3 : (3 : ℝ) - logb 10 (4 ^ 5 - 24 : ℝ) = (0 : ℝ) := by 
      have h511 : logb 10 (4 ^ 5 - 24 : ℝ) = 3 := by
        have h111 : 4 ^ 5 - 24 = (1000 : ℝ) := by norm_num 
        rw [h111] 
        have h1101 : logb 10 (1000) = 3 := by 
          have h222 : (1000 : ℝ) = 10 ^ 3 := by norm_num 
          rw [h222] 
          simp [logb_pow]
        linarith [h1101]
      linarith [h511] 
    linarith [h1, h2, h3]