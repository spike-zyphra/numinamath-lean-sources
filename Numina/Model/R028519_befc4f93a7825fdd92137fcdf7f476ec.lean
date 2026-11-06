import Mathlib

theorem algebra_26726 {f : ℝ → ℝ} (hf : ∀ x, f (f x) = x ^ 2 * f x - x + 1) : f 1 = 1 := by 
  have eq1 := hf 1
  have eq1' : f (f 1) = 1 ^ 2 * f 1 - 1 + 1 := by 
    simpa using eq1
  have eq1'' : f (f 1) = f 1 := by 
    ring_nf at eq1'
    linarith 
  have eq2 := hf 0 
  have eq2' : f (f 0) = (0 : ℝ) ^ 2 * f 0 - (0 : ℝ) + 1 := by 
    simpa using eq2 
  have eq2'' : f (f 0) = 1 := by 
    ring_nf at eq2'
    linarith 
  -- Let's compute f(f(f(1)))
  have eq3 := hf (f 1)
  have eq3' : f (f (f 1)) = (f 1) ^ 2 * f (f 1) - f 1 + 1 := by 
    simpa using eq3 
  -- Since f(f 1) = f 1, we can simplify 
  rw [eq1''] at eq3' 
  -- Now eq3' gives f(f 1) = (f 1) ^ 2 * f 1 - f 1 + 1 
  -- But left side is f(f 1) = f 1 
  have eq3'' : f 1 = (f 1) ^ 2 * f 1 - f 1 + 1 := by 
    linarith [eq3']
  -- Rearrange to get a cubic equation 
  have eq4 : (f 1) ^ 3 - 2 * (f 1) + 1 = 0 := by 
    nlinarith [eq3'']
  -- Factor the cubic equation 
  have eq5 : (f 1 - 1) * ((f 1) ^ 2 + (f 1) - 1) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.mp eq5) with h1 h2 
  · -- Case where f 1 - 1 = 0 
    linarith 
  · -- Case where (f 1) ^ 2 + (f 1) - 1 = 0 
    have eq6 : (f 1) ^ 2 + (f 1) - 1 = 0 := by linarith 
    have eq7 := hf (f 0) 
    have eq8 : f (f (f 0)) = (f 0) ^ 2 * f (f 0) - f 0 + 1 := by 
      simpa using eq7 
    rw [eq2''] at eq8 
    have eq9 : f (f (f 0)) = f 1 := by 
      have h1 : f (f 0) = 1 := eq2''
      rw [h1] 
      all_goals tauto 
    have eq10 : f 1 = (f 0) ^ 2 - f 0 + 1 := by 
      nlinarith [eq8, eq9] 
    -- Now we need to solve the equations system 
    have eq11 : (f 0 - 1) ^ 2 * ((f 0) ^ 2 + 1) = 0 := by
      nlinarith [sq_nonneg (f 0 - 1), sq_nonneg (f 1 - 1), sq_nonneg (f 0 ^ 2 - f 0), sq_nonneg (f 1 ^ 2 - f 1), sq_nonneg (f 0 - f 1)]
    cases' (mul_eq_zero.mp eq11) with eq12 eq13 
    · -- Case where (f 0 - 1) ^ 2 = 0 
      have eq14 : f 0 - 1 = 0 := by 
        apply pow_eq_zero 
        exact eq12 
      have eq15 : f 0 = 1 := by 
        linarith 
      -- Substitute into eq10 
      have eq16 : f 1 = 1 := by 
        rw [eq15] at eq10 
        nlinarith 
      -- Substitute into eq6 
      rw [eq16] at eq6 
      nlinarith 
    · -- Case where (f 0) ^ 2 + 1 = 0 
      have eq14 : (f 0) ^ 2 + 1 = 0 := by 
        linarith 
      nlinarith [sq_nonneg (f 0)]