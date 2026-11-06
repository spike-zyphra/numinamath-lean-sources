import Mathlib

theorem algebra_11162 (a : ℕ → ℝ) (ha1 : a 1 = 1)
    (han : ∀ n, a (n + 1) = (a n + Real.sqrt (a n ^ 2 + 1)) / 2)
    (k : ℤ) (hk : (a 2019) ^ 2 / 1010 < k) :
    k ≥ 1 := by

  have h3 : ∀ (n : ℕ), a (n + 1) > 0 := by 
    intro n 
    induction n with 
    | zero => 
      rw [ha1] 
      norm_num 
    | succ n ih => 
      have h2 : a (n + 1) = (a n + Real.sqrt (a n ^ 2 + 1)) / 2 := by apply han 
      have h3 : a (n + 1) > 0 := by linarith [ih] 
      have h4 : Real.sqrt (a (n + 1) ^ 2 + 1) > 0 := by 
        positivity 
      have h5 : (a (n + 1) + Real.sqrt (a (n + 1) ^ 2 + 1)) / 2 > 0 := by 
        positivity 
      rw [show a (n + 1 + 1) = (a (n + 1) + Real.sqrt (a (n + 1) ^ 2 + 1)) / 2 by apply han] 
      all_goals nlinarith [Real.sqrt_nonneg (a (n + 1) ^ 2 + 1), Real.sqrt_nonneg (a n ^ 2 + 1)]
      all_goals nlinarith [Real.sqrt_nonneg (a (n + 1) ^ 2 + 1), Real.sqrt_nonneg (a n ^ 2 + 1)]
  have h6 : a 2019 > 0 := by 
    apply h3 
  have h7 : (a 2019) ^ 2 > 0 := by 
    nlinarith 
  have h8 : (a 2019) ^ 2 / 1010 > 0 := by 
    positivity 
  by_contra h
  push_neg at h
  have : k ≤ 0 := by linarith 
  have h10 : (k : ℝ) ≤ (0 : ℝ) := by exact_mod_cast this 
  have h11 : (a 2019) ^ 2 / 1010 ≥ (k : ℝ) := by 
    linarith [this, h8] 
  linarith
  all_goals linarith