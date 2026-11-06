import Mathlib

theorem algebra_184387 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
    ¬∃ x : ℝ, b^2 * x^2 + (b^2 + c^2 - a^2) * x + c^2 = 0 := by
  rintro ⟨x, hx⟩
  have h1 : b ^ 2 * x ^ 2 + (b ^ 2 + c ^ 2 - a ^ 2) * x + c ^ 2 = 0 := hx
  have h2 : (b ^ 2 + c ^ 2 - a ^ 2) ^ 2 < 4 * b ^ 2 * c ^ 2 := by
    have h3 : a ^ 2 > (b - c) ^ 2 := by
      have h4 : a > b - c := by
        linarith
      have h5 : a > c - b := by
        linarith
      nlinarith
    have h4 : (b + c) ^ 2 > a ^ 2 := by
      nlinarith
    have h5 : b ^ 2 + c ^ 2 - a ^ 2 < 2 * b * c := by 
      nlinarith [h3]
    have h6 : b ^ 2 + c ^ 2 - a ^ 2 > -2 * b * c := by
      nlinarith [h4]
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  nlinarith [sq_nonneg (b ^ 2 * x + (b ^ 2 + c ^ 2 - a ^ 2) / 2), sq_nonneg (b * c), 
          sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg (a - (b + c)), sq_nonneg (a + b - c), sq_nonneg (a + c - b)]