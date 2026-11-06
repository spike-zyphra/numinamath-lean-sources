import Mathlib
/-The real numbers x and y satisfy the equations
√(3x)(1+1/(x+y) and Real.sqrt (7 * y) * (1 - 1 / (x + y)) = 4 * Real.sqrt 2
Find the numerical value of the ratio y/x-/
theorem algebra_49900 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h1 : Real.sqrt (3 * x) * (1 + 1 / (x + y)) = 2)
    (h2 : Real.sqrt (7 * y) * (1 - 1 / (x + y)) = 4 * Real.sqrt 2) :
    y / x = 6 := by
  have hxy : x + y ≠ 0 := by nlinarith
  -- square on both sides
  have h3 : 3 * x * (1 + 1 / (x + y)) ^ 2 = 4 := by
    have h1' : 0 ≤ Real.sqrt (3 * x) := Real.sqrt_nonneg (3 * x)
    have h2' : 0 ≤ Real.sqrt (7 * y) := Real.sqrt_nonneg (7 * y)
    have h3' : (Real.sqrt (3 * x) * (1 + 1 / (x + y))) ^ 2 = (2) ^ 2 := by
      rw [h1]
    have h4 : (Real.sqrt (3 * x)) ^ 2 = 3 * x := by
      rw [Real.sq_sqrt]
      nlinarith
    nlinarith [h3', h4, sq_nonneg (1 + 1 / (x + y))]
    -- square on both sides
  have h4 : 7 * y * (1 - 1 / (x + y)) ^ 2 = 32 := by
    have h1' : 0 ≤ Real.sqrt (3 * x) := Real.sqrt_nonneg (3 * x)
    have h2' : 0 ≤ Real.sqrt (7 * y) := Real.sqrt_nonneg (7 * y)
    have h3' : (Real.sqrt (7 * y) * (1 - 1 / (x + y))) ^ 2 = (4 * Real.sqrt 2) ^ 2 := by
      rw [h2]
    have h4 : (Real.sqrt (7 * y)) ^ 2 = 7 * y := by
      rw [Real.sq_sqrt]
      nlinarith
    have h5 : (4 * Real.sqrt 2) ^ 2 = 32 := by
      calc
        (4 * Real.sqrt 2) ^ 2 = 4^2 * (Real.sqrt 2)^2 := by ring
        _ = 16 * 2 := by norm_num
        _ = 32 := by norm_num
    nlinarith [h3', h4, h5, Real.sq_sqrt (show 0 ≤ 7 * y by nlinarith), sq_nonneg (1 - 1 / (x + y)), sq_nonneg (Real.sqrt (7 * y)), sq_nonneg (1 - 1 / (x + y))]
  have h6 : x ≠ 0 := by nlinarith
  -- finally, use completing the square to show that y / x = 6
  have h8 : (y / x - 6) = 0 := by
    have h3' : 3 * x * (1 + 1 / (x + y)) ^ 2 = 4 := h3
    have h4' : 7 * y * (1 - 1 / (x + y)) ^ 2 = 32 := h4
    field_simp at h3' h4' ⊢
    nlinarith [Real.sq_sqrt (show 0 ≤ 3 * x by nlinarith), Real.sq_sqrt (show 0 ≤ 7 * y by nlinarith),
      Real.sq_sqrt (show 0 ≤ 2 by norm_num), Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
  linarith
  
