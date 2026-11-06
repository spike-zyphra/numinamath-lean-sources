import Mathlib

/- If $\sum_{n = 0}^{\infty}\cos^{2n}\theta = 5$, what is the value of $\cos{2\theta}$? -/
theorem calculus_15686 (θ : ℝ) (h : ∑' n : ℕ, (Real.cos θ) ^ (2 * n) = 5) :
    Real.cos (2 * θ) = 3 / 5 := by
  replace h : ∑' n : ℕ, (Real.cos θ ^ 2) ^ n = 5 := by
    rw [<-h]
    conv =>
      rhs
      congr
      ext n
      rw [pow_mul]
  -- Use the formula for geometric sum.
  rw [tsum_geometric_of_lt_one, <-one_div, <-one_div_one_div 5] at h
  apply eq_of_one_div_eq_one_div at h
  rw [Real.cos_two_mul]
  linarith only [h]
  -- Resolving remaining goals.
  apply sq_nonneg
  -- Assume cos θ ^ 2 = 1, then the sum does not converge, contradiction. 
  by_contra! g
  replace g : Real.cos θ ^ 2 = 1 := by
    linarith only [g, Real.cos_sq_le_one θ]
  rw [g] at h
  simp at h

