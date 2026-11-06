import Mathlib

theorem algebra_180809 (x y : ℝ) (h : x^2 + y^2 - 6 * x = 0) :
    Real.sqrt (2 * x^2 + y^2 - 4 * x + 5) ∈ Set.Icc (Real.sqrt 5) (Real.sqrt 53) := by
  have h1 : y^2 = 6 * x - x^2 := by 
    nlinarith
  have h2 : 2 * x^2 + y^2 - 4 * x + 5 = x^2 + 2 * x + 5 := by
    rw [h1]
    nlinarith
  have h3 : x^2 + 2 * x + 5 ≥ 5 := by 
    nlinarith [sq_nonneg (x - 3), sq_nonneg (y), sq_nonneg (x * (x - 6)), sq_nonneg (x - 6), h1]
  have h4 : x^2 + 2 * x + 5 ≤ 53 := by 
    nlinarith [sq_nonneg (x - 3), sq_nonneg (y), sq_nonneg (x * (x - 6)), sq_nonneg (x - 6), h1]
  have h5 : 5 ≤ 2 * x^2 + y^2 - 4 * x + 5 := by 
    linarith [h2, h3]
  have h6 : 2 * x^2 + y^2 - 4 * x + 5 ≤ 53 := by 
    linarith [h2, h4]
  constructor
  · -- Show that $\sqrt{5} \leq \sqrt{2 * x^2 + y^2 - 4 * x + 5}$
    have h8 : Real.sqrt 5 ≤ Real.sqrt (2 * x^2 + y^2 - 4 * x + 5) := by
      apply Real.sqrt_le_sqrt
      nlinarith
    exact h8
  · -- Show that $\sqrt{2 * x^2 + y^2 - 4 * x + 5} \leq \sqrt{53}$
    have h10 : Real.sqrt (2 * x^2 + y^2 - 4 * x + 5) ≤ Real.sqrt 53 := by
      apply Real.sqrt_le_sqrt
      nlinarith
    exact h10