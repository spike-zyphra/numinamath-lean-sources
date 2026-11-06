import Mathlib

theorem algebra_253853 (a b : ℕ) (h₀ : a ≤ b) (h₁ : (a + 6 / b : ℝ) * (b + 6 / a : ℝ) = 25) :
    (a = 1 ∧ b = 4) ∨ (a = 2 ∧ b = 2) ∨ (a = 1 ∧ b = 9) ∨ (a = 3 ∧ b = 3) := by

  have h2 : a ≠ 0 := by
    by_contra h
    have h3 : a = 0 := by linarith 
    rw [h3] at h₁
    by_cases h4 : b = 0 
    · -- If b = 0, we have (0 + 6/0)(0 + 6/0)= (0+0)(0+0)=0, so 0=25, which is a contradiction
      rw [h4] at h₁ 
      norm_num at h₁
    · -- If b ≠ 0, then b > 0
      have h5 : b > 0 := by 
        by_contra h6 
        push_neg at h6 
        have : b = 0 := by linarith 
        contradiction 
      have h5' : (b : ℝ) > 0 := by 
          exact_mod_cast h5 
      field_simp at h₁ 
      <;> nlinarith

  have h3 : b ≠ 0 := by 
    by_contra h 
    have h4 : b = 0 := by linarith 
    rw [h4] at h₁ 
    by_cases h5 : a = 0 
    · -- If a = 0, we have (0 + 6/0)(0 + 6/0)= (0+0)(0+0)=0, so 0=25, which is a contradiction 
      rw [h5] at h₁ 
      norm_num at h₁ 
    · -- If a ≠ 0, then a > 0 
      have h6 : a > 0 := by 
        by_contra h7 
        push_neg at h7 
        have : a = 0 := by linarith 
        contradiction 
      -- Simplify h₁ 
      have h6' : (a : ℝ) > 0 := by 
          exact_mod_cast h6 
      field_simp at h₁ 
      <;> nlinarith 

  have ha1 : (a : ℝ) ≠ 0 := by 
    exact_mod_cast h2 
  have hb1 : (b : ℝ) ≠ 0 := by 
    exact_mod_cast h3

  have eq1 : (a + (6 : ℝ) / (b : ℝ)) * (b + (6 : ℝ) / (a : ℝ)) = 25 := by
    simpa using h₁ 

  have eq2 : ((a * (b) + 6) ^ 2 : ℝ) = (25 * (a * (b) : ℝ)) := by
    have h5 : (a * (b) : ℝ) ≠ 0 := by 
      apply mul_ne_zero 
      exact_mod_cast h2 
      exact_mod_cast h3
    have h7' : (a + (6 : ℝ) / (b : ℝ)) * (b + (6 : ℝ) / (a : ℝ)) = ((a * (b) + 6) ^ 2 : ℝ) / (a * (b) : ℝ) := by 
      field_simp 
      <;> ring
    rw [h7'] at eq1 
    field_simp at eq1 ⊢ 
    <;> nlinarith

  have eq3' : ((a * (b)) ^ 2 : ℝ) - 13 * ((a * (b)) : ℝ) + 36 = (0 : ℝ) := by 
    nlinarith

  have factored : ((a * (b) : ℝ) - 4) * ((a * (b) : ℝ) - 9) = (0 : ℝ) := by
    nlinarith [eq3']

  cases' (mul_eq_zero.mp factored) with h4' h9'

  · -- Case where (a * b) = 4 
    have h5' : (a * b : ℝ) = (4 : ℝ) := by 
      linarith 
    have h5 : a * b = 4 := by 
      exact_mod_cast h5'

    -- Now a * b = 4, and a ≤ b. Find pairs (a,b)
    have h6 : a ≤ 4 := by
      nlinarith [show a * b = 4 by linarith, show a ≤ b by linarith]

    have h11 : a * b = 4 := h5

    interval_cases a <;> omega

  · -- Case where (a * b) = 9 
    have h4' : (a * b : ℝ) = (9 : ℝ) := by 
      linarith 
    have h5 : a * b = 9 := by 
      exact_mod_cast h4'

    -- Now a * b = 9, and a ≤ b. Find pairs (a,b)
    have h11 : a ≤ 9 := by 
      nlinarith [show a * b = 9 by linarith, show a ≤ b by linarith]

    have h12 : a * b = 9 := h5

    interval_cases a <;> omega