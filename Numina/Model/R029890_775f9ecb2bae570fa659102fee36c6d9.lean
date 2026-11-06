import Mathlib

open Real

theorem algebra_308941 {f : ℝ → ℝ → ℝ} (hf : ∀ a b, f a b = logb 2 (2^a + 2^b))
    (A B : ℝ) (hA : A = f (f 1 3) 5) (hB : B = f (f 2 4) 6) :
    f 1 (f A B) = 7 := by

  have h1 : f 1 3 = logb 2 10 := by
    rw [hf]
    norm_num

  have hA1 : A = logb 2 42 := by
    rw [hA]
    have h2 : f (f 1 3) 5 = logb 2 42 := by
      rw [hf]
      rw [h1]
      have h3 : (2 : ℝ) ^ (logb 2 10 : ℝ) = (10 : ℝ) := by
        rw [Real.rpow_logb]
        all_goals linarith
      rw [h3]
      have h4 : (2 : ℝ) ^ (5 : ℝ) = (32 : ℝ) := by norm_num
      rw [h4]
      all_goals norm_num [logb]
    exact h2

  have h2 : f 2 4 = logb 2 20 := by
    rw [hf]
    norm_num

  have hB1 : B = logb 2 84 := by
    rw [hB]
    have h3 : f (f 2 4) 6 = logb 2 84 := by
      rw [hf]
      rw [h2]
      have h4 : (2 : ℝ) ^ (logb 2 20 : ℝ) = (20 : ℝ) := by
        rw [Real.rpow_logb]
        all_goals linarith
      rw [h4]
      have h5 : (2 : ℝ) ^ (6 : ℝ) = (64 : ℝ) := by norm_num
      rw [h5]
      all_goals norm_num [logb]
    exact h3

  have h3 : f A B = logb 2 126 := by
    rw [hf]
    rw [hA1, hB1]
    have h4 : (2 : ℝ) ^ (logb 2 42 : ℝ) = (42 : ℝ) := by
      rw [Real.rpow_logb]
      all_goals linarith
    have h5 : (2 : ℝ) ^ (logb 2 84 : ℝ) = (84 : ℝ) := by
      rw [Real.rpow_logb]
      all_goals linarith
    rw [h4, h5]
    all_goals norm_num [logb]

  rw [hf]
  rw [h3]
  have h4 : (2 : ℝ) ^ (1 : ℝ) = (2 : ℝ) := by norm_num
  have h5 : (2 : ℝ) ^ (logb 2 126 : ℝ) = (126 : ℝ) := by
    rw [Real.rpow_logb]
    all_goals linarith
  rw [h4, h5]
  have h6 : logb 2 (2 + 126) = 7 := by
    rw [logb_eq_iff_rpow_eq] <;> norm_num
  exact h6