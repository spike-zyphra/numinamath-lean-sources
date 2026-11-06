import Mathlib

theorem inequalities_598207 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^2 + a * b + b^2) * (b^2 + b * c + c^2) * (c^2 + c * a + a^2) ≥
    (a * b + b * c + c * a)^3 := by 
  have ha1 : a > 0 := ha
  have ha2 : a > 0 := ha
  have ha3 : a > 0 := ha
  
  have hb1 : b > 0 := hb
  have hb2 : b > 0 := hb
  have hb3 : b > 0 := hb
  
  have hc1 : c > 0 := hc
  have hc2 : c > 0 := hc
  have hc3 : c > 0 := hc
  
  -- positivity of main factors
  have ha2_pos : a ^ 2 > 0 := by apply pow_pos; assumption
  have hb2_pos : b ^ 2 > 0 := by apply pow_pos; assumption
  have hc2_pos : c ^ 2 > 0 := by apply pow_pos; assumption
  
  have eq1 : a * b > 0 := mul_pos ha hb
  have eq2 : b * c > 0 := mul_pos hb hc
  have eq3 : c * a > 0 := mul_pos hc ha
  
  have h100 : 0 < a^2 + a * b + b^2 := by nlinarith
  have h101 : 0 < b^2 + b * c + c^2 := by nlinarith
  have h102 : 0 < c^2 + c * a + a^2 := by nlinarith
  
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
            sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
            sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
            mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < a * c from mul_pos ha hc), 
            mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < b * c from mul_pos hb hc), 
            mul_pos (show 0 < a * c from mul_pos ha hc) (show 0 < b * c from mul_pos hb hc)]