import Mathlib

theorem algebra_228217 (x : ℝ) (hx : 0 ≤ 4 + 2 * x ∧ 0 ≤ 6 + 3 * x ∧ 0 ≤ 8 + 4 * x) :
    Real.sqrt (4 + 2 * x) + Real.sqrt (6 + 3 * x) + Real.sqrt (8 + 4 * x) ≠
    9 + 3 * x / 2 := by
  rcases hx with ⟨h1, h2, h3⟩
  by_contra h
  have h4 : Real.sqrt (4 + 2 * x) ≥ 0 := by positivity
  have h5 : Real.sqrt (6 + 3 * x) ≥ 0 := by positivity
  have h6 : Real.sqrt (8 + 4 * x) ≥ 0 := by positivity
  nlinarith [sq_nonneg (Real.sqrt (4 + 2 * x) - 2), sq_nonneg (Real.sqrt (6 + 3 * x) - 3), sq_nonneg (Real.sqrt (8 + 4 * x) - 4),
      Real.sq_sqrt h1, Real.sq_sqrt h2, Real.sq_sqrt h3,
      Real.sqrt_nonneg (4 + 2 * x), Real.sqrt_nonneg (6 + 3 * x),
      Real.sqrt_nonneg (8 + 4 * x),
      mul_nonneg (Real.sqrt_nonneg (4 + 2 * x)) (Real.sqrt_nonneg (6 + 3 * x)),
      mul_nonneg (Real.sqrt_nonneg (6 + 3 * x)) (Real.sqrt_nonneg (8 + 4 * x)),
      mul_nonneg (Real.sqrt_nonneg (4 + 2 * x)) (Real.sqrt_nonneg (8 + 4 * x))
    ]