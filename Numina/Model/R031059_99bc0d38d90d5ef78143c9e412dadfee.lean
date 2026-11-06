import Mathlib

theorem algebra_7915
    (a b c : ℤ)
    (ha : a ≠ b)
    (hb : b ≠ c)
    (hc : a ≠ c)
    (h : (a - 3) * (b - 3) * (c - 3) = 9) :
    a + b + c = 0 ∨ a + b + c = 8 := by

  have h2 : (a - 3) ∣ 9 := by
    use (b - 3) * (c - 3)
    all_goals linarith

  have h3 : (b - 3) ∣ 9 := by
    use (a - 3) * (c - 3)
    all_goals linarith

  have h4 : (c - 3) ∣ 9 := by
    use (a - 3) * (b - 3)
    all_goals linarith

  have h5 : (a - 3) ≤ 9 := by
    apply Int.le_of_dvd (by norm_num) h2

  have h6 : (a - 3) ≥ -9 := by
    have h6 : -(a - 3) ∣ 9 := by
      exact Int.neg_dvd.2 h2
    have h7 : -(a - 3) ≤ 9 := by
      apply Int.le_of_dvd (by norm_num) h6
    linarith

  have h7 : (b - 3) ≤ 9 := by
    apply Int.le_of_dvd (by norm_num) h3

  have h8 : (b - 3) ≥ -9 := by
    have h6 : -(b - 3) ∣ 9 := by
      exact Int.neg_dvd.2 h3
    have h7 : -(b - 3) ≤ 9 := by
      apply Int.le_of_dvd (by norm_num) h6
    linarith

  have h9 : (c - 3) ≤ 9 := by
    apply Int.le_of_dvd (by norm_num) h4

  have h10 : (c - 3) ≥ -9 := by
    have h6 : -(c - 3) ∣ 9 := by
      exact Int.neg_dvd.2 h4
    have h7 : -(c - 3) ≤ 9 := by
      apply Int.le_of_dvd (by norm_num) h6
    linarith

  interval_cases h17 : a - 3 <;> try { 
    omega 
  }
  <;> interval_cases h18 : b - 3 <;> try { 
    omega 
  }
  <;> interval_cases h19 : c - 3 <;> try { 
    omega 
  }