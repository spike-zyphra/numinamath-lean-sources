import Mathlib

theorem algebra_162469 {x y : ℝ} (h1 : 2 * x + Real.sqrt (2 * x + 3 * y) - 3 * y = 5)
    (h2 : 4 * x ^ 2 + 2 * x + 3 * y - 9 * y ^ 2 = 32) :
    x = 17 / 4 ∧ y = 5 / 2 := by
  have h3 : 0 ≤ 2 * x + 3 * y := by
    by_contra h
    push_neg at h
    have h4 : Real.sqrt (2 * x + 3 * y) = 0 := by
      have h5 : 2 * x + 3 * y < 0 := by linarith
      have h6 : Real.sqrt (2 * x + 3 * y) = 0 := by
        rw [Real.sqrt_eq_zero']
        nlinarith
        all_goals nlinarith
      linarith
    rw [h4] at h1
    nlinarith
  have ht2 : Real.sqrt (2 * x + 3 * y) ^ 2 = 2 * x + 3 * y := by
    rw [Real.sq_sqrt]
    linarith
  have ht4 : Real.sqrt (2 * x + 3 * y) = 4 := by
    have ht6 : (Real.sqrt (2 * x + 3 * y) - 4) ^ 2 * (Real.sqrt (2 * x + 3 * y) + 2) = 0 := by
      nlinarith [sq_nonneg (Real.sqrt (2 * x + 3 * y) - 4), sq_nonneg (Real.sqrt (2 * x + 3 * y) ^ 2 - 16), sq_nonneg (2 * x - 3 * y - 1), sq_nonneg (Real.sqrt (2 * x + 3 * y) ^ 2 - 16), Real.sqrt_nonneg (2 * x + 3 * y), sq_nonneg (4 * x - 17), sq_nonneg (y - 5 / 2), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * x + 3 * y by linarith)]
    cases' (mul_eq_zero.mp ht6) with ht7 ht8
    · -- Case where (Real.sqrt (2 * x + 3 * y) - 4) ^ 2 = 0
      have ht9 : Real.sqrt (2 * x + 3 * y) - 4 = 0 := by
        apply pow_eq_zero 
        exact ht7
      linarith
    · -- Case where Real.sqrt (2 * x + 3 * y) + 2 = 0
      -- Real.sqrt (2 * x + 3 * y) ≥ 0 but Real.sqrt (2 * x + 3 * y) = -2
      -- This is impossible
      have ht9 : Real.sqrt (2 * x + 3 * y) = -2 := by linarith
      nlinarith [Real.sqrt_nonneg (2 * x + 3 * y), ht9]
  have h5 : 2 * x + 3 * y = 16 := by
    have ht4 : Real.sqrt (2 * x + 3 * y) = 4 := ht4
    have ht2 : Real.sqrt (2 * x + 3 * y) ^ 2 = 2 * x + 3 * y := by
      rw [Real.sq_sqrt]
      linarith
    rw [ht4] at ht2
    nlinarith
  have h6 : 2 * x - 3 * y = 1 := by
    have ht4 : Real.sqrt (2 * x + 3 * y) = 4 := ht4
    nlinarith [h1, ht4]
  have hx : x = 17 / 4 := by
    nlinarith [h5, h6]
  have hy : y = 5 / 2 := by
    nlinarith [h5, h6]
  exact ⟨hx, hy⟩