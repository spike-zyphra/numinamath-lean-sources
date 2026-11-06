import Mathlib

theorem algebra_4324 {x : ℝ} (hx : x^3-3*x=√(x+2)) (hx' : 64*x^7-112*x^5+56*x^3-7*x+1=0) : x=2 := by
  have h1 : x + 2 ≥ 0 := by
    by_contra h
    push_neg at h
    have h1 : √(x + 2) = 0 := by
      rw [Real.sqrt_eq_zero']
      nlinarith
    rw [h1] at hx
    nlinarith [sq_nonneg (x ^ 2 - 3), sq_nonneg (x + 1), sq_nonneg (x - 2), sq_nonneg (x + 2), sq_nonneg (x ^ 2 - 2 * x), sq_nonneg ((x + 1) * (x + 1)), sq_nonneg (x ^ 2 - 1)]
  have h3 : √(x + 2) ≥ 0 := Real.sqrt_nonneg (x + 2)
  have h4 : x ^ 3 - 3 * x ≥ 0 := by linarith [hx, h3]
  have h5 : (x ^ 3 - 3 * x) ^ 2 = x + 2 := by
    calc
      (x ^ 3 - 3 * x) ^ 2 = (√(x + 2)) ^ 2 := by
        rw [show √(x + 2) = x ^ 3 - 3 * x by linarith [hx]]
      _ = x + 2 := by
        rw [Real.sq_sqrt]
        nlinarith
  nlinarith [sq_nonneg (x ^ 2 - 3), sq_nonneg (x + 1), sq_nonneg (x - 2), sq_nonneg (x + 2), sq_nonneg (x ^ 2 - 2 * x), sq_nonneg ((x + 1) * (x + 1)), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - 2), sq_nonneg (x ^ 2 - 4), sq_nonneg (x - 1), sq_nonneg (x + 1)]