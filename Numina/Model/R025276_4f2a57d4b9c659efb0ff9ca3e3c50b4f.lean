import Mathlib

theorem algebra_4213 {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a^2 + b - c = 160) (h2 : a + b^2 - c = 200) :
    a = 20 ∧ b = 21 ∧ c = 261 := by

  have h3 : (b - a) * (b + a - 1) = 40 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

  have h4 : b - a ∣ 40 := by 
    use b + a - 1 
    all_goals linarith

  have h5 : b - a ≤ 40 := by 
    apply Int.le_of_dvd (by norm_num) h4

  have h6 : b - a ≥ -40 := by 
    have h7 : -(b - a) ∣ 40 := by 
      exact Int.neg_dvd.2 h4 
    have h8 : -(b - a) ≤ 40 := by 
      apply Int.le_of_dvd (by norm_num) h7 
    omega

  interval_cases k : b - a <;> try { 
    omega 
  }
  <;> try { 
    have h11 : a ≤ 32 := by
      nlinarith
    have h12 : b ≤ 38 := by 
      nlinarith 
    have h13 : a ≥ 1 := by linarith 
    have h14 : b ≥ 1 := by linarith 
    interval_cases a <;> try { 
      omega 
    }
  }