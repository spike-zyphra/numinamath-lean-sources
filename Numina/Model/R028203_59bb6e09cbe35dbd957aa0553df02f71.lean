import Mathlib

theorem algebra_2877 (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
(h : 2 * x * y + y = 43 + 2 * x) :
x + y ≤ 16 := by
  have h1 : y ≤ 43 := by
    nlinarith [h, mul_pos hx (show 0 < y by linarith)]
  have h4 : x ≤ 21 := by
    by_contra h5
    push_neg at h5
    -- Assume x > 21. Then we look at possible values of y.
    -- y ≤ 43 from h1.
    have h5 : x > 21 := h5
    have h6 : y ≤ 43 := h1
    interval_cases y <;> try { 
      omega 
    }
    <;> try { 
      nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ), mul_pos hx (show 0 < y by linarith)]
    }
    <;> try { 
      nlinarith [mul_pos hx (show 0 < y by linarith), sq_nonneg (x - 10 : ℤ), sq_nonneg (y - 15 : ℤ)]
    }
    <;> try { 
      nlinarith [mul_pos hx (show 0 < y by linarith), sq_nonneg (x * y : ℤ)]
    }
  interval_cases x <;> try { 
    omega 
  }
  <;> interval_cases y
  <;> omega