import Mathlib

theorem algebra_8168 (a b c d : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (h : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)
    (h1 : (7 - a) * (7 - b) * (7 - c) * (7 - d) = 4) :
    a + b + c + d = 28 := by
  have h2 : (7 - a) * (7 - b) * (7 - c) * (7 - d) = 4 := h1
  have h3 : (7 - a) ∣ 4 := by
    use ((7 - b) * (7 - c) * (7 - d))
    linarith
  have h4 : (7 - b) ∣ 4 := by
    use ((7 - a) * (7 - c) * (7 - d))
    linarith
  have h5 : (7 - c) ∣ 4 := by
    use ((7 - a) * (7 - b) * (7 - d))
    linarith
  have h6 : (7 - d) ∣ 4 := by
    use ((7 - a) * (7 - b) * (7 - c))
    linarith
  have h7 : (7 - a) ≤ 4 := by 
    apply Int.le_of_dvd (by norm_num) h3
  have h8 : (7 - a) ≥ -4 := by 
    have h9 : -(7 - a) ∣ 4 := by
      exact Int.neg_dvd.2 h3
    have h10 : -(7 - a) ≤ 4 := by 
      apply Int.le_of_dvd (by norm_num) h9
    linarith
  have h9 : (7 - b) ≤ 4 := by 
    apply Int.le_of_dvd (by norm_num) h4
  have h10 : (7 - b) ≥ -4 := by 
    have h11 : -(7 - b) ∣ 4 := by
      exact Int.neg_dvd.2 h4
    have h12 : -(7 - b) ≤ 4 := by 
      apply Int.le_of_dvd (by norm_num) h11
    linarith
  have h11 : (7 - c) ≤ 4 := by 
    apply Int.le_of_dvd (by norm_num) h5
  have h12 : (7 - c) ≥ -4 := by 
    have h13 : -(7 - c) ∣ 4 := by
      exact Int.neg_dvd.2 h5
    have h14 : -(7 - c) ≤ 4 := by 
      apply Int.le_of_dvd (by norm_num) h13
    linarith
  have h13 : (7 - d) ≤ 4 := by 
    apply Int.le_of_dvd (by norm_num) h6
  have h14 : (7 - d) ≥ -4 := by 
    have h15 : -(7 - d) ∣ 4 := by
      exact Int.neg_dvd.2 h6
    have h16 : -(7 - d) ≤ 4 := by 
      apply Int.le_of_dvd (by norm_num) h15
    linarith
  -- use finite number of possibilities
  interval_cases h7a : (7 - a) <;> interval_cases h7b : (7 - b) <;> interval_cases h7c : (7 - c) <;> interval_cases h7d : (7 - d) 
    <;> omega