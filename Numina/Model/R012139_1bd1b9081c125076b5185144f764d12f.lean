import Mathlib

theorem algebra_188296 {x y : ℝ} (h₀ : x + y + Real.sqrt (x ^ 2 - y ^ 2) = 12)
  (h₁ : y * Real.sqrt (x ^ 2 - y ^ 2) = 12) :
    (x = 5 ∧ y = 3) ∨ (x = 5 ∧ y = 4)
  := by
  have h2 : 0 ≤ x ^ 2 - y ^ 2 := by
    by_contra h
    push_neg at h
    have h3 : Real.sqrt (x ^ 2 - y ^ 2) = 0 := by
      rw [Real.sqrt_eq_zero']
      nlinarith
      all_goals nlinarith
    rw [h3] at h₀ h₁
    nlinarith [sq_nonneg (x - 5), sq_nonneg (y - 3), sq_nonneg (y - 4)]
  have h3 : Real.sqrt (x ^ 2 - y ^ 2) ≥ 0 := by positivity
  have h4 : Real.sqrt (x ^ 2 - y ^ 2) = 12 - (x + y) := by linarith
  have h6 : (Real.sqrt (x^2 - y^2) ) = 12 - (x + y) := h4
  have h7 : (Real.sqrt (x^2 - y^2))^2 = x^2 - y^2 := by
    rw [Real.sq_sqrt]
    linarith
  have heq3 : y ^ 2 + (x - 12) * y + (72 - 12 * x) = 0 := by
    have h8 : (Real.sqrt (x^2 - y^2) ) = 12 - (x + y) := h4
    have h9 : (Real.sqrt (x^2 - y^2) )^2 = (12 - (x + y) )^2 := by
      rw [h8]
    have h10 : x^2 - y^2 = (12 - (x + y) )^2 := by
      nlinarith [h9, Real.sq_sqrt (show 0 ≤ x ^ 2 - y ^ 2 by linarith)]
    nlinarith [Real.sqrt_nonneg (x^2 - y^2), h₁]
  have h10 : (x - 5) ^ 2 = 0 := by
    have h6 : (Real.sqrt (x^2 - y^2) ) = 12 - (x + y) := h4
    have h11 : Real.sqrt (x^2 - y^2) ≥ 0 := by positivity
    have h12 : x^2 - y^2 ≥ 0 := by
      by_contra h
      push_neg at h
      have : Real.sqrt (x^2 - y^2) = 0 := by
        rw [Real.sqrt_eq_zero']
        nlinarith
        all_goals nlinarith
      rw [this] at h₁ h₀
      nlinarith [sq_nonneg (y), sq_nonneg (x)]
    have h7 : (Real.sqrt (x^2 - y^2))^2 = x^2 - y^2 := by
      rw [Real.sq_sqrt]
      linarith
    -- derived quadratic in y
    have heq3 : y ^ 2 + (x - 12) * y + (72 - 12 * x) = 0 := by
      nlinarith [h6, Real.sq_sqrt (show 0 ≤ x ^ 2 - y ^ 2 by linarith)]
    ring_nf at heq3 
    nlinarith [sq_nonneg (y - 3), sq_nonneg (y - 4), sq_nonneg (x - 5), Real.sqrt_nonneg (x^2 - y^2), sq_nonneg (Real.sqrt (x^2 - y^2)), mul_nonneg (Real.sqrt_nonneg (x^2 - y^2)) (Real.sqrt_nonneg (x^2 - y^2))]
  have hx : x = 5 := by nlinarith
  rw [hx] at heq3
  have hy : (y - 3) * (y - 4) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp hy) with hy1 hy2
  · -- case y = 3
    left
    constructor
    · linarith
    · linarith
  · -- case y = 4
    right
    constructor
    · linarith
    · linarith