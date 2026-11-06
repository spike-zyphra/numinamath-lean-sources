import Mathlib

theorem algebra_287968 :
  {x : ℝ | 16 * x * (x + 1) * (x + 2) * (x + 3) = 9} = 
  {(-3 - Real.sqrt 10) / 2, -3/2, (-3 + Real.sqrt 10) / 2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Assume the equation holds, prove x is one of the three roots.
    intro h 
    have eq1 : 16 * (x^2 + 3 * x) ^ 2 + 32 * (x^2 + 3 * x) - 9 = 0 := by 
      nlinarith [sq_nonneg (x * (x + 3) - (x + 1) * (x + 2)), sq_nonneg (x + 3 / 2)]
    have eq2 : (x^2 + 3 * x - 1 / 4) * (x^2 + 3 * x + 9 / 4) = 0 := by 
      nlinarith [eq1]
    cases' (mul_eq_zero.mp eq2) with eq3 eq4
    · -- Case where $x^2+3 x - 1/4 = 0$.
      have h5 : 4*x^2 + 12*x - 1 = 0 := by 
        nlinarith 
      have h21 : (x - (-3 - Real.sqrt 10) / 2) * (x - (-3 + Real.sqrt 10) / 2) = 0 := by
        nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]
      cases' (mul_eq_zero.mp h21) with h22 h23 
      · -- Case where $x = (-3 - Real.sqrt 10)/2$
        left 
        linarith 
      · -- Case where $x = (-3 + Real.sqrt 10)/2$
        right 
        right 
        linarith 
    · -- Case where $x^2+3 x + 9/4 = 0$.
      have h5 : 4*x^2 + 12*x + 9 = 0 := by 
        nlinarith 
      have h21 : (x + 3 / 2) ^ 2 = 0 := by 
        nlinarith 
      have h6 : x + 3 / 2 = 0 := by 
        apply pow_eq_zero 
        exact h21 
      right 
      left 
      linarith 
  · -- Assume x is one of the three roots, prove the equation.
    rintro (h | h | h)
    · -- Case x = (-3 - Real.sqrt 10) / 2
      rw [h] 
      nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]
    · -- Case x = -3 / 2 
      rw [h] 
      nlinarith 
    · -- Case x = (-3 + Real.sqrt 10) / 2 
      rw [h] 
      nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]