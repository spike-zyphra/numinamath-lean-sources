import Mathlib

theorem inequalities_323079
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    ((2 * a + b + c) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) +
     (a + 2 * b + c) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) +
     (a + b + 2 * c) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2)) ≤ 8 := by 
  have ha1 : 0 < a := ha
  have hb1 : 0 < b := hb
  have hc1 : 0 < c := hc

  have h1 : 2 * a ^ 2 + (b + c) ^ 2 > 0 := by
    positivity
  have h2 : 2 * b ^ 2 + (c + a) ^ 2 > 0 := by
    positivity
  have h3 : 2 * c ^ 2 + (a + b) ^ 2 > 0 := by
    positivity
  
  have h4 : (2 * a + b + c) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) +
     (a + 2 * b + c) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) +
     (a + b + 2 * c) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2) - 8 ≤ 0 := by
    have h' : (2 * a + b + c) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) +
         (a + 2 * b + c) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) +
         (a + b + 2 * c) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2) - 8 =
         ((2 * a + b + c) ^ 2 * (2 * b ^ 2 + (c + a) ^ 2) * (2 * c ^ 2 + (a + b) ^ 2) +
          (a + 2 * b + c) ^ 2 * (2 * a ^ 2 + (b + c) ^ 2) * (2 * c ^ 2 + (a + b) ^ 2) +
          (a + b + 2 * c) ^ 2 * (2 * a ^ 2 + (b + c) ^ 2) * (2 * b ^ 2 + (c + a) ^ 2) - 8 * (2 * a ^ 2 + (b + c) ^ 2) * (2 * b ^ 2 + (c + a) ^ 2) * (2 * c ^ 2 + (a + b) ^ 2))
         / ((2 * a ^ 2 + (b + c) ^ 2) * (2 * b ^ 2 + (c + a) ^ 2) * (2 * c ^ 2 + (a + b) ^ 2)) := by
      field_simp
      ring
    rw [h']
    
    have h5 : (2 * a + b + c) ^ 2 * (2 * b ^ 2 + (c + a) ^ 2) * (2 * c ^ 2 + (a + b) ^ 2) +
          (a + 2 * b + c) ^ 2 * (2 * a ^ 2 + (b + c) ^ 2) * (2 * c ^ 2 + (a + b) ^ 2) +
          (a + b + 2 * c) ^ 2 * (2 * a ^ 2 + (b + c) ^ 2) * (2 * b ^ 2 + (c + a) ^ 2) - 8 * (2 * a ^ 2 + (b + c) ^ 2) * (2 * b ^ 2 + (c + a) ^ 2) * (2 * c ^ 2 + (a + b) ^ 2) ≤ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha1 hb1, mul_pos hb1 hc1, mul_pos ha1 hc1
          ]
    
    apply div_nonpos_of_nonpos_of_nonneg h5 (by positivity)
    
  linarith