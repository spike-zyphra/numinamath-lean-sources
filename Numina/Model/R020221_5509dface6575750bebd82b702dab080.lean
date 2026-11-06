import Mathlib

theorem inequalities_597957 (x y : Fin 3 → ℝ)
    (h : ∑ i, x i ^ 2 ≤ 1) :
    (x 0 * y 0 + x 1 * y 1 + x 2 * y 2 - 1) ^ 2 ≥
    (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 - 1) * (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 - 1) := by 
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h ⊢
  by_cases h1 : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 < 1
  · -- If x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 < 1 then (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 - 1) < 0.
    have h2 : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 - 1 < 0 := by linarith
    by_cases h3 : y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 ≥ 1
    · -- If y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 ≥ 1 then y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 - 1 ≥ 0.
      have h4 : y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 - 1 ≥ 0 := by linarith
      have h5 : (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 - 1) * (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 - 1) ≤ 0 := by
        nlinarith
      have h6 : (x 0 * y 0 + x 1 * y 1 + x 2 * y 2 - 1) ^ 2 ≥ 0 := by positivity
      linarith
    by_cases h4 : y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 < 1
    · -- If y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 < 1 then y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 - 1 < 0.
      have h5 : y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 - 1 < 0 := by linarith
      have h6 : (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 - 1) * (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 - 1) > 0 := by
        nlinarith
      nlinarith [sq_nonneg (x 0 * y 1 - x 1 * y 0), sq_nonneg (x 0 * y 2 - x 2 * y 0),
          sq_nonneg (x 1 * y 2 - x 2 * y 1), sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1),
          sq_nonneg (x 2 - y 2), sq_nonneg ((x 0 * y 0 + x 1 * y 1 + x 2 * y 2) - (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2)),
          mul_nonneg (show (0 : ℝ) ≤ 1 - (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) by linarith) (show (0 : ℝ) ≤ 1 - (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) by linarith)]
    linarith
  · -- If x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1 then (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 - 1) = 0.
    have h2 : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1 := by linarith
    have h3 : (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 - 1) = 0 := by linarith
    rw [h3]
    simp
    <;> nlinarith [sq_nonneg (x 0 * y 1 - x 1 * y 0), sq_nonneg (x 0 * y 2 - x 2 * y 0),
        sq_nonneg (x 1 * y 2 - x 2 * y 1), sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1),
        sq_nonneg (x 2 - y 2), sq_nonneg ((x 0 * y 0 + x 1 * y 1 + x 2 * y 2) - (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2))]