import Mathlib

theorem algebra_7248 : IsLeast {y : ℝ | ∃ x, y = (x + 1) * (x + 2) * (x + 3) * (x + 4) + 2021} 2020 := by
  constructor
  · -- Show 2020 is achievable by proving it equals the expression evaluated at (-5 ±√5)/2
    use (-5 + Real.sqrt 5) / 2
    nlinarith [sq_nonneg (Real.sqrt 5), Real.sqrt_nonneg 5, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
    
  · -- Show that 2020 is the least value by proving that all values in the set are >= 2020
    rintro y hy
    rcases hy with ⟨x, hx⟩
    
    have h : (x + 1) * (x + 2) * (x + 3) * (x + 4) + 2021 = (x^2 + 5 * x + 5) ^ 2 + 2020 := by ring
    rw [h] at hx
    have h2 : (x^2 + 5 * x + 5) ^ 2 ≥ 0 := by
      apply sq_nonneg
    linarith