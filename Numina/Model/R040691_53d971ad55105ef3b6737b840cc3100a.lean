import Mathlib

theorem algebra_265184 (x y : ℤ) (h : y^2 + 3 * x^2 * y^2 = 30 * x^2 + 517) :
    3 * x^2 * y^2 = 588 := by
  have h1 : y^2 + 3 * x^2 * y^2 = 30 * x^2 + 517 := h
  have h2 : y^2 * (3 * x^2 + 1) = 30 * x^2 + 517 := by
    linarith [h]
  have h3 : (3 * x^2 + 1) ∣ 507 := by 
    have eq2 : (y^2 - 10) * (3 * x^2 + 1) = 507 := by
      nlinarith
    use y^2 - 10
    all_goals nlinarith
  have h4 : (3 * x^2 + 1) ≤ 507 := by 
    apply Int.le_of_dvd (by norm_num) h3
  have h5 : x^2 ≤ 168 := by 
    nlinarith
  have h6 : x ≤ 12 := by nlinarith [show x^2 ≥ 0 from sq_nonneg x]
  have h7 : x ≥ -12 := by nlinarith [show x^2 ≥ 0 from sq_nonneg x]
  interval_cases x <;> try { 
    omega
  } <;> try { 
    have h2 : y ≤ 32 := by nlinarith
    have h3 : y ≥ -32 := by nlinarith
    interval_cases y <;> omega
  }