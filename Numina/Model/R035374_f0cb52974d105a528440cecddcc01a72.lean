import Mathlib

theorem algebra_251576 {x y : ℕ} (h : x ^ 2 + 12 = y ^ 2) :
    x + y = 6 := by
  have h1 : y > x := by
    by_contra h1
    push_neg at h1
    have h2 : y ≤ x := h1
    have h3 : y ^ 2 ≤ x ^ 2 := by
      nlinarith
    omega
  have h4 : y ≤ 7 := by
    nlinarith [sq_nonneg (y - x : ℤ), sq_nonneg (y + x : ℤ),
      show x ^ 2 + 12 = y ^ 2 by linarith
    ]
  have h5 : x ≤ 7 := by
    nlinarith
  interval_cases y <;> try { 
    omega
  }
  <;> interval_cases x <;> omega