import Mathlib

theorem algebra_52175 {x y : ℤ} (h : y^2 + 3 * x^2 * y^2 = 30 * x^2 + 517) :
    3 * x^2 * y^2 = 588 := by
  have h1 : y^2 * (3 * x^2 + 1) = 30 * x^2 + 517 := by 
    linarith
  have h2 : y^2 * (3 * x^2 + 1) = 10 * (3 * x^2 + 1) + 507 := by
    nlinarith [h1]
  -- We can write the equation as: (y^2 - 10)(3 * x^2 + 1) = 507
  have h3 : (y^2 - 10) * (3 * x^2 + 1) = 507 := by
    linarith [h2]
  -- We need to bound the possible values of x and y.
  have h4 : (3 * x^2 + 1) ∣ 507 := by 
    use (y^2 - 10)
    all_goals linarith [h3]
  have h7 : (3 * x^2 + 1) ≤ 507 := by
    exact Int.le_of_dvd (by norm_num) h4
  have h8 : x^2 ≤ 168 := by 
      nlinarith
  have h9 : x ≤ 12 := by 
      nlinarith [sq_nonneg (x : ℤ)]
  have h9' : x ≥ -12 := by 
      nlinarith [sq_nonneg (x : ℤ)]
  -- Now use exhaustive search.
  have h5' : (3 * x^2 + 1) ≤ 507 := h7
  interval_cases x <;> try { 
    omega
  } <;> try { 
    have h10 : y^2 ≤ 517 := by
      nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ)]
    have h11 : y ≤ 22 := by 
      nlinarith [sq_nonneg (y : ℤ)]
    have h12 : y ≥ -22 := by 
      nlinarith [sq_nonneg (y : ℤ)]
    interval_cases y <;> omega
  }