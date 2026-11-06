import Mathlib

theorem algebra_266566 (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (h : a^2 + b = b^2 + a + 62) :
    (a, b) = (32, 31) ∨ (a, b) = (17, 15) := by
  have eq1 : (a - b) * (a + b - 1) = 62 := by
    nlinarith
  have h2 : (a - b) * (a + b - 1) = 62 := eq1
  have h3 : (a - b) ∣ 62 := by
    use (a + b - 1)
    all_goals nlinarith
  have h4 : (a - b) ≤ 62 := by
    exact Int.le_of_dvd (by norm_num) h3
  have h5 : (a - b) ≥ -62 := by
    have h6 : (- (a - b)) ∣ 62 := by
      exact Int.neg_dvd.2 h3
    have h7 : - (a - b) ≤ 62 := by
      exact Int.le_of_dvd (by norm_num) h6
    linarith
  interval_cases h6 : (a - b) <;> norm_num at h2 h6 ⊢
  <;> norm_num [Prod.ext_iff] at *
  <;> try { 
    omega 
  }
  <;> tauto