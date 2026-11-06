import Mathlib

theorem algebra_182958 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : 1 / (a + b) = 7.2) (h2 : 1 / (a + c) = 9) (h3 : 1 / (b + c) = 12) :
    1 / (a + b + c) = 6 := by

  -- Ensure denominators are non-zero
  have eq1 : a + b ≠ 0 := by
    by_contra h
    have h4 : 1 / (a + b) = 0 := by
      rw [h]
      norm_num 
    linarith [h1, h4]

  have eq2 : a + c ≠ 0 := by
    by_contra h
    have h4 : 1 / (a + c) = 0 := by
      rw [h]
      norm_num 
    linarith [h2, h4]

  have eq3 : b + c ≠ 0 := by
    by_contra h
    have h4 : 1 / (b + c) = 0 := by
      rw [h]
      norm_num 
    linarith [h3, h4]

  -- Convert reciprocal equations to direct linear equations
  have eq4 : a + b = 1 / (7.2 : ℝ) := by 
    have h4 : 1 / (a + b) = (7.2 : ℝ) := by
      linarith
    field_simp [eq1] at h4 ⊢
    linarith

  have eq5 : a + c = 1 / (9 : ℝ) := by
    have h5 : 1 / (a + c) = (9 : ℝ) := by 
      linarith
    field_simp [eq2] at h5 ⊢
    linarith

  have eq6 : b + c = 1 / (12 : ℝ) := by 
    have h6 : 1 / (b + c) = (12 : ℝ) := by 
      linarith
    field_simp [eq3] at h6 ⊢
    linarith

  -- Sum the three equations: (a + b) + (a + c) + (b + c) = 1/7.2 + 1/9 + 1/12
  -- This simplifies to 2(a + b + c) = sum of reciprocals
  -- Therefore a + b + c = (sum of reciprocals)/2
  have eq7 : a + b + c = ( (1 / (7.2 : ℝ)) + (1 / (9 : ℝ)) + (1 / (12 : ℝ)) ) / 2 := by
    linarith [eq4, eq5, eq6]

  -- Calculate sum of reciprocals divided by 2 to get 1/6
  have eq8 : a + b + c = (1 : ℝ) / 6 := by 
    have eq9 : ( (1 / (7.2 : ℝ)) + (1 / (9 : ℝ)) + (1 / (12 : ℝ)) ) / 2 = (1 : ℝ) / 6 := by
      norm_num
    linarith [eq7, eq9]

  -- Final reciprocal to convert back to the desired result
  have eq10 : 1 / (a + b + c) = 6 := by 
    rw [eq8]
    field_simp

  exact eq10