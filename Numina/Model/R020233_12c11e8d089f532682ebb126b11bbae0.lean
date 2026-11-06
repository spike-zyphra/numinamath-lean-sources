import Mathlib

theorem algebra_11872 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : ∃ d, a + 19 * d = 1 / a ∧ a + 200 * d = 1 / b ∧ a + 2011 * d = 1 / c) :
    1992 * a * c - 1811 * b * c - 181 * a * b = 0 := by
  rcases h with ⟨d, h1, h2, h3⟩

  -- For the first equation, multiply both sides by a to clear the fraction
  field_simp [ha] at h1
  have eq1 : a^2 + 19 * a * d - 1 = 0 := by
    nlinarith

  -- For the second equation, multiply both sides by b to clear the fraction
  field_simp [hb] at h2
  have eq2 : a * b + 200 * b * d - 1 = 0 := by
    nlinarith
  
  -- For the third equation, multiply both sides by c to clear the fraction
  have eq3 : a * c + 2011 * c * d - 1 = 0 := by
    field_simp [hc] at h3
    nlinarith
  
  -- Manipulation to solve the variables
  have eq4 : 19 * a * d = 1 - a^2 := by
    linarith [eq1, h1]

  -- Manipulation to solve the variables
  have eq5 : a * c + 2011 * c * d - 1 = 0 := by 
    nlinarith [eq3]

  -- Solve the variables and substitute into the expression
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, sq_nonneg (a * b * c), sq_nonneg (a * b * d), sq_nonneg (a * c * d), sq_nonneg (b * c * d), sq_nonneg (d), sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c))]