import Mathlib

theorem algebra_252052 :
    {x : ℝ | (1 + x^4) / (1 + x)^4 = 1 / 2 ∧ x ≠ -1 ∧ x ≠ 0} = 
    {1 + Real.sqrt 3 + Real.sqrt (3 + 2 * Real.sqrt 3), 1 + Real.sqrt 3 - Real.sqrt (3 + 2 * Real.sqrt 3)} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Forward: if x satisfies the equation, then it's one of the two roots
    intro h
    rcases h with ⟨h_eq, hx1, hx2⟩
    have h1 : (1 + x) ^ 4 ≠ 0 := by
      have h2 : (1 + x) ≠ 0 := by
        intro h3
        apply hx1
        linarith
      have h3 : (1 + x) ^ 4 ≠ 0 := by
        apply pow_ne_zero 4
        exact h2
      assumption
    have h2 : 2 * (1 + x^4) = (1 + x)^4 := by
      field_simp [h1] at h_eq
      nlinarith
    have h3 : (x ^ 4) - 4 * (x ^ 3) - 6 * (x ^ 2) - 4 * x + 1 = 0 := by
      nlinarith [sq_nonneg (x ^ 2 - 2 * x - 1), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 1)]
    have h4 : (x ^ 2 + (-2 - 2 * Real.sqrt 3) * x + 1) * (x ^ 2 + (-2 + 2 * Real.sqrt 3) * x + 1) = 0 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (x ^ 2 - 2 * x - 1), sq_nonneg (x -1), sq_nonneg (x +1)]
    cases (mul_eq_zero.1 h4) with
    | inl h5 =>
      have h5' : x ^ 2 + (-2 - 2 * Real.sqrt 3) * x + 1 = 0 := by
        linarith
      have h6 : (x - (1 + Real.sqrt 3 + Real.sqrt (3 + 2 * Real.sqrt 3))) * (x - (1 + Real.sqrt 3 - Real.sqrt (3 + 2 * Real.sqrt 3))) = 0 := by 
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (3 + 2 * Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 + 2 * Real.sqrt 3 : ℝ) by positivity), sq_nonneg (x ^ 2 - 2 * x - 1), sq_nonneg (x - 1), sq_nonneg (x + 1)]
      cases (mul_eq_zero.1 h6) with
      | inl h7 =>
        left
        nlinarith
      | inr h7 =>
        right
        nlinarith
    | inr h5 =>
      -- The quadratic x^2 + (-2 + 2*sqrt(3)) x + 1 has complex roots
      exfalso
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (x ^ 2 - 2 * x - 1), sq_nonneg (x -1), sq_nonneg (x +1)]
  · -- Backward: both expressions satisfy the equation
    rintro (h_eq | h_eq)
    · -- First expression
      rw [h_eq]
      constructor
      · -- Show it satisfies the equation
        have h1 : (1 + (1 + Real.sqrt 3 + Real.sqrt (3 + 2 * Real.sqrt 3)) ) ≠ 0 := by
          nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (3 + 2 * Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 + 2 * Real.sqrt 3) by positivity), sq_nonneg (Real.sqrt (3 + 2 * Real.sqrt 3) - Real.sqrt 3), sq_nonneg (Real.sqrt (3 + 2 * Real.sqrt 3) + Real.sqrt 3 - 2), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg (3 + 2 * Real.sqrt 3)) ]
        field_simp [h1]
        <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (3 + 2 * Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 + 2 * Real.sqrt 3) by positivity), sq_nonneg (Real.sqrt (3 + 2 * Real.sqrt 3) - Real.sqrt 3), sq_nonneg (Real.sqrt (3 + 2 * Real.sqrt 3) + Real.sqrt 3 - 2), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg (3 + 2 * Real.sqrt 3)) ]
        all_goals
          norm_num
          all_goals norm_num
          all_goals nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (3 + 2 * Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 + 2 * Real.sqrt 3) by positivity)]
      constructor
      · -- Show x ≠ -1
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (3 + 2 * Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 + 2 * Real.sqrt 3) by positivity), sq_nonneg (Real.sqrt (3 + 2 * Real.sqrt 3) - Real.sqrt 3), sq_nonneg (Real.sqrt (3 + 2 * Real.sqrt 3) + Real.sqrt 3 - 2), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg (3 + 2 * Real.sqrt 3)) ]
      · -- Show x ≠ 0
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (3 + 2 * Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 + 2 * Real.sqrt 3) by positivity), sq_nonneg (Real.sqrt (3 + 2 * Real.sqrt 3) - Real.sqrt 3), sq_nonneg (Real.sqrt (3 + 2 * Real.sqrt 3) + Real.sqrt 3 - 2), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg (3 + 2 * Real.sqrt 3)) ]
    · -- Second expression
      rw [h_eq]
      constructor
      · -- Show it satisfies the equation
        have h1 : (1 + (1 + Real.sqrt 3 - Real.sqrt (3 + 2 * Real.sqrt 3)) ) ≠ 0 := by
          nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (3 + 2 * Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 + 2 * Real.sqrt 3) by positivity), sq_nonneg (Real.sqrt (3 + 2 * Real.sqrt 3) - Real.sqrt 3), sq_nonneg (Real.sqrt (3 + 2 * Real.sqrt 3) + Real.sqrt 3 - 2), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg (3 + 2 * Real.sqrt 3)) ]
        field_simp [h1]
        <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (3 + 2 * Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 + 2 * Real.sqrt 3) by positivity), sq_nonneg (Real.sqrt (3 + 2 * Real.sqrt 3) - Real.sqrt 3), sq_nonneg (Real.sqrt (3 + 2 * Real.sqrt 3) + Real.sqrt 3 - 2), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg (3 + 2 * Real.sqrt 3)) ]
        all_goals
          norm_num
          all_goals norm_num
          all_goals nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (3 + 2 * Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 + 2 * Real.sqrt 3) by positivity)]
      constructor
      · -- Show x ≠ -1
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (3 + 2 * Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 + 2 * Real.sqrt 3) by positivity), sq_nonneg (Real.sqrt (3 + 2 * Real.sqrt 3) - Real.sqrt 3), sq_nonneg (Real.sqrt (3 + 2 * Real.sqrt 3) + Real.sqrt 3 - 2), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg (3 + 2 * Real.sqrt 3)) ]
      · -- Show x ≠ 0
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (3 + 2 * Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 + 2 * Real.sqrt 3) by positivity), sq_nonneg (Real.sqrt (3 + 2 * Real.sqrt 3) - Real.sqrt 3), sq_nonneg (Real.sqrt (3 + 2 * Real.sqrt 3) + Real.sqrt 3 - 2), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg (3 + 2 * Real.sqrt 3)) ]