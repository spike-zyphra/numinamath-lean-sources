import Mathlib

theorem algebra_11908 : {x : ℝ | x ≠ -1 ∧ ((13 * x - x ^ 2) / (x + 1)) * (x + (13 - x) / (x + 1)) = 42} = {1, 6, 3 + Real.sqrt 2, 3 - Real.sqrt 2} := by
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor 
  · -- Assume x ∈ LHS, prove x ∈ RHS 
    rintro ⟨hx1, heq⟩ 
    have eq1 : x + 1 ≠ 0 := by
      intro h
      apply hx1 
      linarith
    have eq2 : ((13 * x - x ^ 2) / (x + 1)) * (x + (13 - x) / (x + 1)) = ( (13 * x - x^2) * (x^2 + 13) ) / (x + 1)^2 := by
      field_simp [eq1]
      ring
    rw [eq2] at heq 
    have eq3 : ( (13 * x - x^2) * (x^2 + 13) ) / (x + 1)^2 = 42 := heq 
    have eq4 : (13 * x - x^2) * (x^2 + 13) = 42 * (x + 1) ^2 := by 
      have eq5 : ( (13 * x - x^2) * (x^2 + 13) ) / (x + 1)^2 = 42 := eq3
      field_simp [eq1] at eq5 ⊢ 
      all_goals nlinarith 
    have h_eq : (x - 1) * (x - 6) * (x^2 - 6 * x + 7) = 0 := by 
      nlinarith [ sq_nonneg (x^2) , sq_nonneg ((x -1) * (x -6)), sq_nonneg (x -3) ]
    cases' (mul_eq_zero.mp h_eq) with h1 h2 
    · -- Case (x - 1) * (x - 6) = 0 
      cases' (mul_eq_zero.mp h1) with h3 h4 
      · -- Case x - 1 = 0, so x = 1 
        left 
        linarith 
      · -- Case x - 6 = 0, so x = 6 
        right 
        left 
        linarith 
    · -- Case x^2 - 6 * x + 7 = 0 
      have h3 : x^2 - 6 * x + 7 = 0 := h2 
      have h4 : (x - (3 + Real.sqrt 2)) * (x - (3 - Real.sqrt 2)) = 0 := by
        nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), sq_nonneg (x - 3) ]
      cases' (mul_eq_zero.mp h4) with h5 h6
      · -- Case x - (3 + Real.sqrt 2) = 0, so x = 3 + Real.sqrt 2 
        right 
        right 
        left 
        linarith 
      · -- Case x - (3 - Real.sqrt 2) = 0, so x = 3 - Real.sqrt 2 
        right 
        right 
        right 
        linarith 
  · -- Backward direction: if x is one of the values, it's a solution. 
    rintro (rfl | rfl | rfl | rfl)
    · -- Show that 1 is a solution 
      constructor 
      · norm_num 
      · -- Show that x = 1 satisfies the equation 
        norm_num 
    · -- Show that 6 is a solution
      constructor
      · norm_num 
      · -- Show that x = 6 satisfies the equation 
        norm_num 
    · -- Show that 3 + Real.sqrt 2 is a solution 
      constructor 
      · -- Show that it's not -1 
        by_contra h_eq 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) ]
      · -- Show that x = 3 + Real.sqrt 2 satisfies the equation 
        field_simp [(show (3 + Real.sqrt 2 : ℝ) + 1 ≠ 0 by 
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) ]
        )]
        nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) ]
    · -- Show that 3 - Real.sqrt 2 is a solution 
      constructor 
      · -- Show that it's not -1 
        by_contra h_eq 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) ]
      · -- Show that x = 3 - Real.sqrt 2 satisfies the equation 
        field_simp [(show (3 - Real.sqrt 2 : ℝ) + 1 ≠ 0 by 
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) ]
        )]
        nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) ]