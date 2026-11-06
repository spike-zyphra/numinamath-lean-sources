import Mathlib
theorem algebra_68918 (x y z : ℤ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h1 : x^2 + y - z = 100) (h2 : x + y^2 - z = 124) :
    (x, y, z) = (12, 13, 57) := by

  -- From here, need to solve the equation and impose the constraints.
  -- We have a system of two quadratic equations and found above manipulation within substituting
  -- Final step here is to exhaustive
  -- Solution from manual solving is (12, 13, 57)
  have eq1 : (x - y) * (1 - x - y) = 24 := by
    nlinarith
  have h4 : (x - y) ∣ 24 := by
    use (1 - x - y)
    all_goals nlinarith
  have h7 : (x - y) ≤ 24 := by
    apply Int.le_of_dvd (by norm_num) h4
  have h8 : (x - y) ≥ -24 := by
    have h7 : (- (x - y)) ∣ 24 := by
      exact Int.neg_dvd.2 h4
    have h8 : - (x - y) ≤ 24 := by
      apply Int.le_of_dvd (by norm_num) h7
    omega
  interval_cases h9 : (x - y) <;> try { 
    omega
  }
  <;> try { 
    have h10 : x ≤ 24 := by
      nlinarith
    have h11 : y ≤ 24 := by
      nlinarith
    interval_cases x <;> interval_cases y
    <;> norm_num at eq1 h1 h2
    <;> try { 
      omega
    }
    <;> try { 
      simp [Prod.ext_iff] at *
      <;> norm_num at *
      <;> omega
    }
  }