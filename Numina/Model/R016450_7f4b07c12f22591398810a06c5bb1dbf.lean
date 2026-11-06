import Mathlib

theorem algebra_273899 (c : ℝ) :
    (∃ x : ℝ, x^2 + c * x + 2 = 0) ∨ (∃ x : ℝ, x^2 + 2 * x + c = 2) := by
  by_cases h : c ^ 2 ≥ 8
  · -- If c^2 ≥ 8, then the first equation has real roots.
    left
    use (-c + Real.sqrt (c ^ 2 - 8)) / 2
    nlinarith [Real.sqrt_nonneg (c ^ 2 - 8), Real.sq_sqrt (show c ^ 2 - 8 ≥ 0 by linarith)]
  · -- If c^2 < 8, then the second equation has real roots.
    have h2 : 12 - 4 * c ≥ 0 := by
      by_contra h12
      push_neg at h12
      nlinarith [sq_nonneg (c), sq_nonneg (c - 3)]
    right
    use -1 + Real.sqrt (12 - 4 * c) / 2
    nlinarith [Real.sqrt_nonneg (12 - 4 * c), Real.sq_sqrt (show 12 - 4 * c ≥ 0 by linarith)]