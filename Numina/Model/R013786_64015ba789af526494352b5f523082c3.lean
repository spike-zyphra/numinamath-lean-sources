import Mathlib

theorem algebra_220011 (a b c d r : ℤ) (h₀ : a ≠ b) (h₁ : a ≠ c) (h₂ : a ≠ d)
    (h₃ : b ≠ c) (h₄ : b ≠ d) (h₅ : c ≠ d) (h₆ : (r - a) * (r - b) * (r - c) * (r - d) - 4 = 0) :
    4 * r = a + b + c + d := by
  have h7 : (r - a) * (r - b) * (r - c) * (r - d) = 4 := by
    linarith
  have h8 : (r - a) ∣ 4 := by
    use ( (r - b) * (r - c) * (r - d) )
    linarith
  have h9 : (r - a) ≤ 4 := by
    apply Int.le_of_dvd (by norm_num) h8
  have h10 : (r - a) ≥ -4 := by
    have h11 : -(r - a) ∣ 4 := by
      exact Int.neg_dvd.2 h8
    have h12 : -(r - a) ≤ 4 := by
      apply Int.le_of_dvd (by norm_num) h11
    linarith
  have h11 : (r - b) ∣ 4 := by
    use ( (r - a) * (r - c) * (r - d) )
    nlinarith
  have h12 : (r - b) ≤ 4 := by
    apply Int.le_of_dvd (by norm_num) h11
  have h13 : (r - b) ≥ -4 := by
    have h11 : -(r - b) ∣ 4 := by
      exact Int.neg_dvd.2 h11
    have h12 : -(r - b) ≤ 4 := by
      apply Int.le_of_dvd (by norm_num) h11
    linarith
  have h14 : (r - c) ∣ 4 := by
    use ( (r - a) * (r - b) * (r - d) )
    nlinarith
  have h15 : (r - c) ≤ 4 := by
    apply Int.le_of_dvd (by norm_num) h14
  have h16 : (r - c) ≥ -4 := by
    have h11 : -(r - c) ∣ 4 := by
      exact Int.neg_dvd.2 h14
    have h12 : -(r - c) ≤ 4 := by
      apply Int.le_of_dvd (by norm_num) h11
    linarith
  have h17 : (r - d) ∣ 4 := by
    use ( (r - a) * (r - b) * (r - c) )
    nlinarith
  have h18 : (r - d) ≤ 4 := by
    apply Int.le_of_dvd (by norm_num) h17
  have h19 : (r - d) ≥ -4 := by
    have h11 : -(r - d) ∣ 4 := by
      exact Int.neg_dvd.2 h17
    have h12 : -(r - d) ≤ 4 := by
      apply Int.le_of_dvd (by norm_num) h11
    linarith
  interval_cases h : (r - a) <;> interval_cases k : (r - b) <;> 
    interval_cases m : (r - c) <;> omega