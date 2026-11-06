import Mathlib

theorem algebra_159939 (x y : ℝ) (h₀ : 3 * x + Real.sqrt (3 * x - y) + y = 6) (h₁ : 9 * x ^ 2 + 3 * x - y - y ^ 2 = 36) :
    (x, y) = (2, -3) ∨ (x, y) = (6, -18) := by
  let t := Real.sqrt (3 * x - y)
  have ht2 : t = Real.sqrt (3 * x - y) := rfl
  have h3 : 3 * x - y ≥ 0 := by
    by_contra h
    push_neg at h
    have h4 : Real.sqrt (3 * x - y) = 0 := by
      rw [Real.sqrt_eq_zero']
      all_goals
      nlinarith
    rw [h4] at h₀
    nlinarith
  
  have ht4 : t ^ 2 = 3 * x - y := by
    have h5 : 3 * x - y ≥ 0 := h3
    have : (Real.sqrt (3 * x - y)) ^ 2 = 3 * x - y := Real.sq_sqrt h5
    rw [ht2] at *
    linarith

  have ht5 : y = 3 * x - t^2 := by
    nlinarith [ht4]

  have ht6 : t ^ 2 - 6 * x - t + 6 = 0 := by 
    have h6 : y = 3 * x - t ^ 2 := by 
      nlinarith [ht4, sq_nonneg (t)]
    nlinarith [h₀, h6, Real.sqrt_nonneg (3 * x - y), sq_nonneg (t), Real.sq_sqrt (show (0 : ℝ) ≤ 3 * x - y by linarith)]

  have ht9 : -t^4 + 6 * x * t^2 + t^2 - 36 = 0 := by 
    have h6 : y = 3 * x - t ^ 2 := by 
      nlinarith [ht4, sq_nonneg (t)]
    nlinarith [h₁, h6, Real.sqrt_nonneg (3 * x - y), sq_nonneg (t), Real.sq_sqrt (show (0 : ℝ) ≤ 3 * x - y by linarith)]

  have h5 : t ≥ 0 := by
    have : t = Real.sqrt (3 * x - y) := ht2
    have h6 : 3 * x - y ≥ 0 := h3
    have : Real.sqrt (3 * x - y) ≥ 0 := Real.sqrt_nonneg (3 * x - y)
    linarith

  have h4 : (t - 3) * (t - 6) = 0 := by
    nlinarith [sq_nonneg (t - 3), sq_nonneg (t - 6), ht6, ht9, sq_nonneg (t^2 - 36), sq_nonneg (t^2), sq_nonneg ((3 * x - y) - t^2), h3]

  have h6 : t = 3 ∨ t = 6 := by
    cases' (mul_eq_zero.mp h4) with h7 h8
    · -- Case where t - 3 = 0
      left
      nlinarith
    · -- Case where t - 6 = 0
      right
      nlinarith

  cases h6 with
  | inl h8 => 
    have hx : x = 2 := by
      nlinarith [h8, ht6]
    have hy : y = -3 := by
      nlinarith [h8, ht6, hx, ht5]
    left
    simp [Prod.ext_iff, hx, hy]
  | inr h8 =>
    have hx : x = 6 := by
      nlinarith [h8, ht6]
    have hy : y = -18 := by
      nlinarith [h8, ht6, hx, ht5]
    right
    simp [Prod.ext_iff, hx, hy]