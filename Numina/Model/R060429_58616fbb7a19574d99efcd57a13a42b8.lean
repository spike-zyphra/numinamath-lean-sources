import Mathlib

theorem inequalities_86448 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a * b / (a + b) + b * c / (b + c) + c * a / (c + a)) ≤ (a + b + c) / 2 := by
  have h1 : a * b / (a + b) ≤ (a + b) / 4 := by
    have h2 : a * b ≤ ((a + b) ^ 2) / 4 := by
      nlinarith [sq_nonneg (a - b)]
    have h3 : 0 < a + b := by linarith
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (a - b)]
    
  have h2 : b * c / (b + c) ≤ (b + c) / 4 := by
    have h4 : b * c ≤ ((b + c) ^ 2) / 4 := by
      nlinarith [sq_nonneg (b - c)]
    have h3 : 0 < b + c := by linarith
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (b - c)]
    
  have h3 : c * a / (c + a) ≤ (c + a) / 4 := by
    have h5 : c * a ≤ ((c + a) ^ 2) / 4 := by
      nlinarith [sq_nonneg (c - a)]
    have h3 : 0 < c + a := by linarith
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (c - a)]
    
  linarith [h1, h2, h3]
  all_goals nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]