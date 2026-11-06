import Mathlib

theorem algebra_9397 (x y : ℤ) (hx : x > 0) (hy : y > 0) (h : 2 * x ^ 2 + 5 * x * y + 2 * y ^ 2 = 2006) : (x = 3 ∧ y = 28) ∨ (x=28 ∧ y=3) := by 
  have h2 : (2 * x + y) * (x + 2 * y) = 2006 := by
    nlinarith 
  -- Now that we know x and y both within reasonable bounds. 
  -- Prove the bounds.
  have h5 : x ≤ 31 := by
    nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - 31), sq_nonneg (y - 31),
      sq_nonneg (x + y), sq_nonneg (x - y)
    ]
  have h6 : y ≤ 31 := by
    nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - 31), sq_nonneg (y - 31),
      sq_nonneg (x + y), sq_nonneg (x - y)
    ]
  interval_cases x <;> try { 
    omega 
  }
  <;> try { 
    interval_cases y <;> omega 
  }