import Mathlib

theorem algebra_3326 (x y : ℤ) (hx : x > 0) (hy : y > 0) (h : x * y + 3 * x - 5 * y = 27) :
x ^ 2 + y ≤ 65 := by
  have h1 : (x - 5) * (y + 3) = 12 := by 
    nlinarith
  have h2 : x - 5 ∣ 12 := by
    use y + 3
    all_goals linarith
  have h3 : x - 5 ≤ 12 := by
    apply Int.le_of_dvd (by norm_num) h2
  have h4 : x - 5 ≥ -12 := by
    have h5 : (- (x - 5)) ∣ 12 := by
      exact Int.neg_dvd.2 h2
    have h6 : - (x - 5) ≤ 12 := by
      apply Int.le_of_dvd (by norm_num) h5
    linarith
  interval_cases h20 : x - 5 <;> try { 
    omega
  }
  <;> try { 
    all_goals 
    try { 
      have hx1 : x = 6 := by 
        nlinarith
      have hy1 : y = 9 := by 
        nlinarith
      rw [hx1, hy1]
      all_goals omega
    }
    <;> try { 
      have hx1 : x = 7 := by 
        nlinarith
      have hy1 : y = 3 := by 
        nlinarith
      rw [hx1, hy1]
      all_goals omega
    }
    <;> try { 
      have hx1 : x = 8 := by 
        nlinarith
      have hy1 : y = 1 := by 
        nlinarith
      rw [hx1, hy1]
      all_goals omega
    }
    <;> try { 
      exfalso
      nlinarith
      all_goals omega
    }
    <;> try { 
      nlinarith
    }
  }
  <;> try { 
    all_goals
    omega
    <;> tauto
  }
  <;> try { 
    all_goals
    omega
  }
  <;> try { 
    all_goals
    linarith
  }