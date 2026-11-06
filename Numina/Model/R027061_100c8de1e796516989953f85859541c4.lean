import Mathlib

theorem algebra_322471 (x y z : ℤ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h1 : 6 * x - y - z = 18) (h2 : x ^ 2 + y ^ 2 + z ^ 2 = 1987) :
    x = 13 ∧ y = 27 ∧ z = 33 ∨ x = 13 ∧ y = 33 ∧ z = 27 := by 
  have h3 : y + z = 6 * x - 18 := by 
    nlinarith
  -- substitution into the second equation
  -- x ^ 2 + y ^ 2 + z ^ 2 = 1987
  have h4 : z = 6 * x - 18 - y := by 
    omega
  rw [h4] at h2
  -- bounded variables x, y, z
  have h5 : x ≤ 44 := by 
    nlinarith [sq_nonneg (x - 44 : ℤ), sq_nonneg (y - 44 : ℤ), sq_nonneg (z - 44 : ℤ)]
  have h6 : x > 3 := by
    nlinarith [sq_pos_of_pos hy, sq_pos_of_pos hz]
  interval_cases x <;> try { 
    norm_num at h1 h2 ⊢
    <;> try { 
      have h7 : y ≤ 66 := by
        nlinarith
      interval_cases y <;> omega 
    }
    <;> try { 
      omega 
    }
  }