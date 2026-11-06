import Mathlib

theorem algebra_296328 {a b c : ℝ} (hb : 0 < b) (h1 : a^2 - 2 * a * b + c^2 = 0) (h2 : b * c > a^2) :
    b > c ∧ c > a := by
  have h3 : c^2 = 2 * a * b - a^2 := by
    nlinarith
  have h4 : 2 * a * b - a^2 ≥ 0 := by 
    nlinarith [sq_nonneg c, h3]
  have hc : 0 < c := by 
    nlinarith [h2, hb, sq_nonneg a]
  have ha : 0 < a := by 
    nlinarith [sq_pos_of_pos hb, sq_nonneg (c - a), sq_nonneg (c + a), h3, hc]
  have h5 : c > a := by 
    have h6 : c ^ 2 > a ^ 2 := by 
      nlinarith [h3, ha, hb, sq_pos_of_pos hc]
    nlinarith [sq_nonneg (c - a), hc, ha]
  have h7 : b > a := by 
    nlinarith [h2, h5, sq_nonneg (b - a), sq_nonneg (c - a), ha, sq_nonneg (c - a)]
  have h8 : b > c := by 
    nlinarith [sq_nonneg (b - c), h5, h7, sq_nonneg (c - a), sq_nonneg (b - a), h3, h2, hb, ha, hc]
  constructor
  · exact h8
  · exact h5