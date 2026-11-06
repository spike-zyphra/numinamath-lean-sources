import Mathlib

theorem algebra_93836 : ¬∃ x y z : ℤ,
  x ^ 2 - 3 * x * y + 2 * y ^ 2 - z ^ 2 = 31 ∧
  -x ^ 2 + 6 * y * z + 2 * z ^ 2 = 44 ∧
  x ^ 2 + x * y + 8 * z ^ 2 = 100 := by
  rintro ⟨x, y, z, h1, h2, h3⟩
  have h4 : z ≤ 3 := by
    nlinarith [sq_nonneg (z : ℤ), sq_nonneg (x + y : ℤ), sq_nonneg (y : ℤ), sq_nonneg (x : ℤ)]
  have h5 : z ≥ -3 := by
    nlinarith [sq_nonneg (z : ℤ), sq_nonneg (x + y : ℤ), sq_nonneg (y : ℤ), sq_nonneg (x : ℤ)]
  interval_cases z <;> try { 
    omega 
  }
  <;> norm_num at h1 h2 h3
  <;> try { 
    have h6 : x ≤ 20 := by nlinarith 
    have h7 : x ≥ -20 := by nlinarith 
    have h8 : y ≤ 20 := by nlinarith 
    have h9 : y ≥ -20 := by nlinarith 
    interval_cases x <;> try { 
      omega 
    } 
  }
  <;> try { 
    have h10 : y ≤ 20 := by nlinarith 
    have h11 : y ≥ -20 := by nlinarith 
    interval_cases y <;> omega 
  }