import Mathlib
open Real

theorem algebra_2488 (a : ℝ) (h : a + sqrt (a^2) + a^(3 / 3) = 0) :
    abs (a - 1) + abs (a + 1) = 2 := by
  have h1 : sqrt (a ^ 2) = abs a := by 
    rw [Real.sqrt_sq_eq_abs]
  -- Express the term a^(3/3) in the hypothesis in a simplified way
  have h2 : a ^ (3 / 3 : ℝ) = a := by
    have h3 : (3 / 3 : ℝ) = (1 : ℝ) := by norm_num 
    rw [h3] 
    simp 
  -- We need to establish: a + |a| + a = 0 from h and h1, h2.
  have h3 : a + abs a + a = 0 := by
    have eq1 : sqrt (a ^ 2) = abs a := h1
    have eq2 : a ^ (3 / 3 : ℝ) = a := h2 
    have eq3 : a + sqrt (a ^ 2) + a ^ (3 / 3 : ℝ) = a + abs a + a := by 
      rw [eq1, eq2]
      all_goals linarith 
    linarith [h, eq3]
  -- Now from a + |a| + a = 0, we can write 2*a + |a| = 0.
  have h4 : 2 * a + abs a = 0 := by 
    linarith [h3]
  -- Now, we will consider two cases based on the value of a.
  by_cases h5 : a ≥ 0 
  · -- If a ≥ 0, then |a| = a. 
    have h6 : abs a = a := by
      rw [abs_of_nonneg h5]
    rw [h6] at h4 
    -- Now, we have 2*a + a = 0, which gives a = 0. 
    have ha0 : a = 0 := by 
      linarith 
    -- Now that we know a = 0, compute the result. 
    rw [ha0]
    norm_num [abs]
    all_goals try { 
      norm_num [abs]
      all_goals try { tauto } 
    }
  · -- If a < 0, then |a| = -a. 
    have h7 : abs a = -a := by 
      rw [abs_of_neg (lt_of_not_ge h5)]
    rw [h7] at h4 
    -- Now, we have 2*a - a = 0, which gives a = 0. 
    -- This is a contradiction as it breaks the hypothesis. 
    have ha0 : a = 0 := by 
      linarith 
    -- We need to handle the contradiction.
    linarith [ha0, lt_of_not_ge h5]