import Mathlib

theorem algebra_297323 {x y : ℝ} (hy : y ≠ 0) (h1 : Real.sqrt (x + 1 / y) - Real.sqrt (x + y - 3) = Real.sqrt 3) (h2 : 2 * x + y + 1 / y = 6) :
    (x, y) = (2, 1) ∨ (x, y) = (4, -1) := by
  -- The first equation involving square roots can be rewritten
  have h2' : 2 * x + y + 1 / y = 6 := h2
  have eq1 : (x + 1 / y) + (x + y) = 6 := by
    calc
      (x + 1 / y) + (x + y) = 2 * x + y + 1 / y := by ring
      _ = 6 := h2
  
  -- Let's handle the first equation
  have h4 : Real.sqrt (x + 1 / y) - Real.sqrt (x + y - 3) = Real.sqrt 3 := h1

  -- Need to ensure square roots are valid
  have h1_pos : x + 1 / y ≥ 0 := by
    by_contra h
    push_neg at h
    have h8 : Real.sqrt (x + 1 / y) = 0 := by
      rw [Real.sqrt_eq_zero']
      all_goals nlinarith
      all_goals nlinarith
    have h9 : Real.sqrt (x + y - 3) = -Real.sqrt 3 := by
      nlinarith [h8, h4]
    have h11 : Real.sqrt (x + y - 3) ≥ 0 := by apply Real.sqrt_nonneg
    have h12 : Real.sqrt 3 ≥ 0 := by apply Real.sqrt_nonneg
    have h13 : Real.sqrt (x + y - 3) ≥ 0 := by apply Real.sqrt_nonneg
    nlinarith [Real.sqrt_pos.mpr (show 0 < 3 by norm_num : (0 : ℝ) < 3),
      h9, Real.sqrt_nonneg (x + y - 3), Real.sqrt_nonneg 3
      ]
      -- same side of it
  
  have h2_pos : x + y - 3 ≥ 0 := by
    by_contra h
    push_neg at h
    have h8 : Real.sqrt (x + y - 3) = 0 := by
      rw [Real.sqrt_eq_zero']
      all_goals nlinarith
      all_goals nlinarith
    have h9 : Real.sqrt (x + 1 / y) = Real.sqrt 3 := by 
      nlinarith [h8, h4]
    have h10 : (Real.sqrt (x + 1 / y)) ^ 2 = (Real.sqrt 3) ^ 2 := by
      rw [h9]
    have h11 : (Real.sqrt (x + 1 / y)) ^ 2 = x + 1 / y := by
      apply Real.sq_sqrt
      have h1_pos' : x + 1 / y ≥ 0 := by assumption
      linarith
    have h12 : (Real.sqrt (3 : ℝ)) ^ 2 = (3 : ℝ) := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
    nlinarith
  
  have h5 : Real.sqrt (x + 1 / y) = Real.sqrt (x + y - 3) + Real.sqrt 3 := by
    nlinarith
  
  -- Now square both sides
  have h6 : (Real.sqrt (x + 1 / y)) ^ 2 = (Real.sqrt (x + y - 3) + Real.sqrt 3) ^ 2 := by
    rw [h5]
  
  -- Simplify the left side 
  have h7 : (Real.sqrt (x + 1 / y)) ^ 2 = x + 1 / y := by
    apply Real.sq_sqrt
    have h1_pos' : x + 1 / y ≥ 0 := by assumption
    linarith
  
  -- Simplify the right side 
  have h16 : (Real.sqrt (x + y - 3))^2 = x + y - 3 := by
    apply Real.sq_sqrt
    have h2_pos' : x + y - 3 ≥ 0 := by assumption
    linarith
  
  have h17 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have h8 : (Real.sqrt (x + y - 3) + Real.sqrt 3)^2 = (Real.sqrt (x + y - 3))^2 + (Real.sqrt 3)^2 + 2 * (Real.sqrt (x + y - 3) * Real.sqrt 3) := by ring
  
  rw [h7] at h6
  rw [h8] at h6
  -- From here, introduce h16 + h17 into h6 and combine
  -- with h6 and eq1 to form quadratic literials
  rw [h16, h17] at h6
  have h8 : (x - 2) * (x - 4) = 0 := by
    field_simp [show y ≠ 0 by assumption] at eq1 h2 h6
    nlinarith [Real.sqrt_nonneg (x + 1 / y), Real.sqrt_nonneg (x + y - 3), Real.sqrt_nonneg 3, 
          sq_nonneg (Real.sqrt (x + 1 / y) - Real.sqrt (x + y - 3) - Real.sqrt 3), 
          sq_nonneg (Real.sqrt (x + 1 / y) + Real.sqrt (x + y - 3) + Real.sqrt 3),
          sq_nonneg (y - 1), sq_nonneg (y + 1),
          mul_nonneg (Real.sqrt_nonneg (x + 1 / y)) (Real.sqrt_nonneg (x + y - 3)), 
          mul_nonneg (Real.sqrt_nonneg (x + 1 / y)) (Real.sqrt_nonneg 3), 
          Real.sqrt_nonneg (x + 1 / y), Real.sqrt_nonneg (x + y - 3), Real.sqrt_nonneg 3
    ]
  
  cases' (mul_eq_zero.mp h8) with h9 h10
  · -- First case: solve the equality for x and then y from the approach 
    have hx2 : x = 2 := by linarith
    have hy1 : y = 1 := by 
      have h3' : 2 * x + y + 1 / y = 6 := h2
      rw [hx2] at h3'
      field_simp [hy] at h3'
      nlinarith 
    left
    exact Prod.ext hx2 hy1
  
  · -- Case analysis: solve for the possible derivation of x and y
    have hx4 : x = 4 := by linarith 
    have hy2 : y = -1 := by 
      have h3' : 2 * x + y + 1 / y = 6 := h2
      rw [hx4] at h3'
      field_simp [hy] at h3'
      nlinarith 
    right
    exact Prod.ext hx4 hy2
  all_goals linarith