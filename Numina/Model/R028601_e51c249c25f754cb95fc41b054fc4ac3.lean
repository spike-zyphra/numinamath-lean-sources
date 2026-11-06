import Mathlib

open Real

theorem inequalities_598537 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Real.sqrt (a^2 + 8 * b * c) + Real.sqrt (b^2 + 8 * c * a) + Real.sqrt (c^2 + 8 * a * b) ≤
    3 * (a + b + c) := by 
  have h2 : (Real.sqrt (a^2 + 8 * b * c) + Real.sqrt (b^2 + 8 * c * a) + Real.sqrt (c^2 + 8 * a * b)) ^ 2 ≤ 3 * (a^2 + 8 * b * c + (b^2 + 8 * c * a) + (c^2 + 8 * a * b)) := by
    have h4 : (Real.sqrt (a^2 + 8 * b * c)) ^ 2 = a^2 + 8 * b * c := Real.sq_sqrt (by positivity)
    have h5 : (Real.sqrt (b^2 + 8 * c * a)) ^ 2 = b^2 + 8 * c * a := Real.sq_sqrt (by positivity)
    have h6 : (Real.sqrt (c^2 + 8 * a * b)) ^ 2 = c^2 + 8 * a * b := Real.sq_sqrt (by positivity)
    nlinarith [sq_nonneg (Real.sqrt (a^2 + 8 * b * c) - Real.sqrt (b^2 + 8 * c * a)), sq_nonneg (Real.sqrt (b^2 + 8 * c * a) - Real.sqrt (c^2 + 8 * a * b)), sq_nonneg (Real.sqrt (c^2 + 8 * a * b) - Real.sqrt (a^2 + 8 * b * c)), 
      Real.sqrt_nonneg (a^2 + 8 * b * c), Real.sqrt_nonneg (b^2 + 8 * c * a), Real.sqrt_nonneg (c^2 + 8 * a * b)]
  have h3' : 3 * (a^2 + 8 * b * c + (b^2 + 8 * c * a) + (c^2 + 8 * a * b)) ≤ 9 * (a + b + c) ^ 2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have h2' : (Real.sqrt (a^2 + 8 * b * c) + Real.sqrt (b^2 + 8 * c * a) + Real.sqrt (c^2 + 8 * a * b)) ^ 2 ≤ 9 * (a + b + c) ^ 2 := by
    nlinarith
  have h4' : Real.sqrt (a^2 + 8 * b * c) + Real.sqrt (b^2 + 8 * c * a) + Real.sqrt (c^2 + 8 * a * b) ≤ 3 * (a + b + c) := by
    have h7 : (Real.sqrt (a^2 + 8 * b * c) + Real.sqrt (b^2 + 8 * c * a) + Real.sqrt (c^2 + 8 * a * b)) ≤ 3 * (a + b + c) := by
      nlinarith [Real.sqrt_nonneg (a^2 + 8 * b * c), Real.sqrt_nonneg (b^2 + 8 * c * a), Real.sqrt_nonneg (c^2 + 8 * a * b), sq_nonneg (3 * (a + b + c)), sq_nonneg (Real.sqrt (a^2 + 8 * b * c) + Real.sqrt (b^2 + 8 * c * a) + Real.sqrt (c^2 + 8 * a * b) - 3 * (a + b + c)), Real.sqrt_nonneg (a^2 + 8 * b * c), Real.sqrt_nonneg (b^2 + 8 * c * a), Real.sqrt_nonneg (c^2 + 8 * a * b)]
    exact h7
  exact h4'