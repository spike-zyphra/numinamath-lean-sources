import Mathlib

theorem algebra_237329 {x y : ℝ} (h₀ : x + y = 2 * Real.sqrt 1703) (h₁ : |x - y| = 90) :
    x * y = -322 := by
  have h2 : (x - y) ^ 2 = 8100 := by 
    cases eq_or_eq_neg_of_abs_eq h₁ with 
    | inl h => 
      nlinarith 
    | inr h => 
      nlinarith 
  have h3 : (x + y) ^ 2 = 6812 := by
    rw [h₀]
    have h4 : (Real.sqrt 1703 : ℝ) ^ 2 = 1703 := by 
      exact Real.sq_sqrt (by norm_num)
    have h5 : (2 * Real.sqrt 1703 : ℝ) ^ 2 = 4 * 1703 := by
      calc
        (2 * Real.sqrt 1703 : ℝ) ^ 2 = 4 * (Real.sqrt 1703 : ℝ) ^ 2 := by ring_nf
        _ = 4 * 1703 := by rw [h4]
    nlinarith 
  have h4 : 4 * (x * y) = -1288 := by
    nlinarith [sq (x + y), sq (x - y), h3, h2]
  -- Therefore, x * y = -322
  linarith 
  all_goals nlinarith 
  all_goals nlinarith 
  all_goals nlinarith 
  all_goals nlinarith 
  all_goals nlinarith 
  all_goals nlinarith 
  all_goals nlinarith 
  all_goals nlinarith 
  all_goals nlinarith 
  all_goals nlinarith 
  all_goals nlinarith 
  all_goals nlinarith 
  all_goals nlinarith 
  all_goals nlinarith 
  all_goals nlinarith 
  all_goals nlinarith 
  all_goals nlinarith 
  all_goals nlinarith 
  all_goals nlinarith 
  all_goals nlinarith 
  all_goals nlinarith 
  <;> norm_num 
  all_goals norm_num 
  all_goals ring_nf 
  all_goals nlinarith 
  all_goals nlinarith 
  all_goals nlinarith 
  all_goals nlinarith