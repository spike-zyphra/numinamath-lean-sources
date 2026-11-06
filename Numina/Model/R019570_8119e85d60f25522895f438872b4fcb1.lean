import Mathlib

theorem algebra_112164 (x y : ℤ) (hx : 0 < x) (hy : 0 < y)
    (h : x^2 = y^2 + 7 * y + 6) :
    (x, y) = (6, 3) := by

  have h1 : x^2 = y^2 + 7 * y + 6 := by 
    linarith

  have h2 : y ≤ 12 := by
    by_contra h2
    push_neg at h2 
    -- Assume y > 12.
    have h3 : x ≤ y + 3 := by
      nlinarith [sq_nonneg (x - (y + 3)), sq_nonneg (x + (y + 3)), h1, sq_nonneg (y)]
    have h4 : x ≥ y + 3 := by
      nlinarith [sq_nonneg (x - (y + 3)), sq_nonneg (x + (y + 3)), h1, sq_nonneg (y)]
    have h5 : x = y + 3 := by
      linarith
    have h6 : y = 3 := by
      nlinarith [sq_nonneg (x - (y + 3)), h1, h5, sq_nonneg (y)]
    omega
  -- Now we have a finite upper bound on y. Similarly, establish bound for x
  have h3 : y ≤ 12 := h2

  have h4 : x ≤ 25 := by
    nlinarith [sq_nonneg (x - y - 3), sq_nonneg (y - 3), h1, sq_nonneg (x * 6), h3]

  -- Now use exhaustive checking
  have h8 : y > 0 := by linarith 
  have h9 : x > 0 := by linarith 
  have h11 : x ≤ 25 := h4
  have h12 : y ≤ 12 := h2

  -- Using exhaustive checking
  interval_cases y <;> try { 
    omega 
  } <;> try { 
    interval_cases x <;> norm_num [Prod.ext_iff] at h1 ⊢ <;> tauto
  }