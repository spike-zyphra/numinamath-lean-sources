import Mathlib

theorem Algebra_609170 {x y z : ℤ} (hx : x > 0) (hy : y > 0) (hz : z > 0) (h1 : x ^ 2 + y - z = 100)
  (h2 : x + y ^ 2 - z = 124) : x = 12 ∧ y = 13 ∧ z = 57 := by 
  have eq2 : (y - x) * (y + x - 1) = 24 := by 
    nlinarith 
  have h11 : (y - x) ∣ 24 := by
    use y + x - 1 
    all_goals 
      nlinarith
  -- The factors of 24
  have h6 : (y - x) ≤ 24 := by
    apply Int.le_of_dvd (by norm_num) h11
  -- The possible negative factors
  have h6' : (y - x) ≥ -24 := by
    have h7 : -(y - x) ∣ 24 := by
      exact Int.neg_dvd.2 h11
    have h8 : -(y - x) ≤ 24 := by
      apply Int.le_of_dvd (by norm_num) h7 
    omega
  interval_cases k : y - x <;> try { 
    omega 
  }
  <;> try { 
    have hx1 : x ≤ 30 := by nlinarith
    have hy1 : y ≤ 30 := by nlinarith
    interval_cases x <;> try { 
      omega 
    }
  }