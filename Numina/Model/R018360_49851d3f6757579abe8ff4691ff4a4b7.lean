import Mathlib

theorem inequalities_600233 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a / (3 * a ^ 2 + b ^ 2 + 2 * a * c) + b / (3 * b ^ 2 + c ^ 2 + 2 * a * b) +
     c / (3 * c ^ 2 + a ^ 2 + 2 * b * c)) ≤ 3 / (2 * (a + b + c)) ∧
    (a / (2 * a ^ 2 + b ^ 2 + c ^ 2) + b / (2 * b ^ 2 + c ^ 2 + a ^ 2) +
     c / (2 * c ^ 2 + a ^ 2 + b ^ 2)) ≤ 9 / (4 * (a + b + c)) := by 
  constructor
  · -- Prove the first inequality
    have hx : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
    have h1 : a / (3 * a ^ 2 + b ^ 2 + 2 * a * c) + b / (3 * b ^ 2 + c ^ 2 + 2 * a * b) + c / (3 * c ^ 2 + a ^ 2 + 2 * b * c) - 3 / (2 * (a + b + c)) ≤ 0 := by 
      have h3 : 0 < 2 * (a + b + c) := by nlinarith
      have h4 : 0 < (3 * a ^ 2 + b ^ 2 + 2 * a * c) * (3 * b ^ 2 + c ^ 2 + 2 * a * b) * (3 * c ^ 2 + a ^ 2 + 2 * b * c) * (2 * (a + b + c)) := by positivity 
      have h5 : a / (3 * a ^ 2 + b ^ 2 + 2 * a * c) + b / (3 * b ^ 2 + c ^ 2 + 2 * a * b) + c / (3 * c ^ 2 + a ^ 2 + 2 * b * c) - 3 / (2 * (a + b + c)) ≤ 0 := by 
        have h51 : a / (3 * a ^ 2 + b ^ 2 + 2 * a * c) + b / (3 * b ^ 2 + c ^ 2 + 2 * a * b) + c / (3 * c ^ 2 + a ^ 2 + 2 * b * c) - 3 / (2 * (a + b + c)) = 
          ( a * (3 * b ^ 2 + c ^ 2 + 2 * a * b) * (3 * c ^ 2 + a ^ 2 + 2 * b * c) * (2 * (a + b + c)) + b * (3 * a ^ 2 + b ^ 2 + 2 * a * c) * (3 * c ^ 2 + a ^ 2 + 2 * b * c) * (2 * (a + b + c)) + c * (3 * a ^ 2 + b ^ 2 + 2 * a * c) * (3 * b ^ 2 + c ^ 2 + 2 * a * b) * (2 * (a + b + c)) - 3 * (3 * a ^ 2 + b ^ 2 + 2 * a * c) * (3 * b ^ 2 + c ^ 2 + 2 * a * b) * (3 * c ^ 2 + a ^ 2 + 2 * b * c)) / ((3 * a ^ 2 + b ^ 2 + 2 * a * c) * (3 * b ^ 2 + c ^ 2 + 2 * a * b) * (3 * c ^ 2 + a ^ 2 + 2 * b * c) * (2 * (a + b + c))) := by 
          field_simp 
          ring 
        rw [h51] 
        apply div_nonpos_of_nonpos_of_nonneg 
        · -- To prove the numerator is nonpositive 
          nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
            sq_nonneg (a * (a - b)), sq_nonneg (a * (b - c)), sq_nonneg (a * (c - a)), 
            sq_nonneg (b * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (b * (c - a)), 
            sq_nonneg (c * (a - b)), sq_nonneg (c * (b - c)), sq_nonneg (c * (c - a)), 
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
            sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a)]
        · -- Denominator is nonneg, actually positive. 
          positivity 
      linarith
    linarith
  · -- Prove the second inequality
    have h2 : a / (2 * a ^ 2 + b ^ 2 + c ^ 2) + b / (2 * b ^ 2 + c ^ 2 + a ^ 2) + c / (2 * c ^ 2 + a ^ 2 + b ^ 2) - 9 / (4 * (a + b + c)) ≤ 0 := by
      have h14 : 0 < 4 * (a + b + c) := by nlinarith
      have h4 : 0 < (2 * a ^ 2 + b ^ 2 + c ^ 2) * (2 * b ^ 2 + c ^ 2 + a ^ 2) * (2 * c ^ 2 + a ^ 2 + b ^ 2) * (4 * (a + b + c)) := by positivity
      have h6 : a / (2 * a ^ 2 + b ^ 2 + c ^ 2) + b / (2 * b ^ 2 + c ^ 2 + a ^ 2) + c / (2 * c ^ 2 + a ^ 2 + b ^ 2) - 9 / (4 * (a + b + c)) ≤ 0 := by 
        have h41 : a / (2 * a ^ 2 + b ^ 2 + c ^ 2) + b / (2 * b ^ 2 + c ^ 2 + a ^ 2) + c / (2 * c ^ 2 + a ^ 2 + b ^ 2) - 9 / (4 * (a + b + c)) = 
          ( a * (2 * b ^ 2 + c ^ 2 + a ^ 2) * (2 * c ^ 2 + a ^ 2 + b ^ 2) * (4 * (a + b + c)) + b * (2 * a ^ 2 + b ^ 2 + c ^ 2) * (2 * c ^ 2 + a ^ 2 + b ^ 2) * (4 * (a + b + c)) + c * (2 * a ^ 2 + b ^ 2 + c ^ 2) * (2 * b ^ 2 + c ^ 2 + a ^ 2) * (4 * (a + b + c)) - 9 * (2 * a ^ 2 + b ^ 2 + c ^ 2) * (2 * b ^ 2 + c ^ 2 + a ^ 2) * (2 * c ^ 2 + a ^ 2 + b ^ 2) ) / ((2 * a ^ 2 + b ^ 2 + c ^ 2) * (2 * b ^ 2 + c ^ 2 + a ^ 2) * (2 * c ^ 2 + a ^ 2 + b ^ 2) * (4 * (a + b + c))) := by 
          field_simp 
          ring 
        rw [h41]
        apply div_nonpos_of_nonpos_of_nonneg
        · -- To prove the numerator is nonpositive
          nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a * (a - b)), sq_nonneg (a * (b - c)), sq_nonneg (a * (c - a)), 
            sq_nonneg (b * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (b * (c - a)), 
            sq_nonneg (c * (a - b)), sq_nonneg (c * (b - c)), sq_nonneg (c * (c - a)), 
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
            sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a)]
        · -- Denominator is nonneg, actually positive. 
          positivity
      linarith 
    linarith