import Mathlib

theorem algebra_197969 {a b c: ℕ} (h: a * b * c + a * b + b * c + a * c + a + b + c = 164) :
    a * b * c = 80 ∨ a * b * c = 0:= by
  have h1 : (a + 1) * (b + 1) * (c + 1) = 165 := by
    nlinarith
  have h2 : (a + 1) ∣ 165 := by
    use (b + 1) * (c + 1)
    linarith [h1]
  have h3 : (a + 1) ≤ 165 := by 
    exact Nat.le_of_dvd (by norm_num) h2
  have h4 : (b + 1) ∣ 165 := by
    use (a + 1) * (c + 1)
    linarith [h1]
  have h5 : (b + 1) ≤ 165 := by 
    exact Nat.le_of_dvd (by norm_num) h4
  have h6 : (c + 1) ∣ 165 := by
    use (a + 1) * (b + 1)
    linarith [h1]
  have h7 : (c + 1) ≤ 165 := by 
    exact Nat.le_of_dvd (by norm_num) h6
  have h8 : a ≤ 164 := by
    omega
  have h9 : b ≤ 164 := by
    omega
  have h10 : c ≤ 164 := by
    omega
  interval_cases a <;> try { 
    omega 
  } <;> try { 
    interval_cases b <;> try { 
      omega 
    } 
  }