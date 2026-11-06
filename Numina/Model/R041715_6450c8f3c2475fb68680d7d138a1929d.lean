import Mathlib

theorem inequalities_605946 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 2 / 3) :
    (a * b / (a + b) + b * c / (b + c) + c * a / (c + a)) ≥
    (a + b + c) / (a ^ 3 + b ^ 3 + c ^ 3) := by
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : 0 < c := hc
  have h21 : 0 < a * b := by positivity
  have h22 : 0 < b * c := by positivity
  have h23 : 0 < c * a := by positivity
  have h24 : 0 < a * b * c := by positivity
  have h24' : a * b * c = 2 / 3 := habc
  have h7 : a * b / (a + b) + b * c / (b + c) + c * a / (c + a) - (a + b + c) / (a ^ 3 + b ^ 3 + c ^ 3) ≥ 0 := by 
    have h13 : 0 < (a + b) := by positivity
    have h14 : 0 < (b + c) := by positivity
    have h15 : 0 < (c + a) := by positivity
    have h12 : 0 < a ^ 3 + b ^ 3 + c ^ 3 := by positivity
    have h7' : a * b / (a + b) + b * c / (b + c) + c * a / (c + a) - (a + b + c) / (a ^ 3 + b ^ 3 + c ^ 3) =
          (a * b * (b + c) * (c + a) * (a ^ 3 + b ^ 3 + c ^ 3) + b * c * (a + b) * (c + a) * (a ^ 3 + b ^ 3 + c ^ 3) + 
          c * a * (a + b) * (b + c) * (a ^ 3 + b ^ 3 + c ^ 3) - 
          (a + b + c) * (a + b) * (b + c) * (c + a)
          ) / ((a + b) * (b + c) * (c + a) * (a ^ 3 + b ^ 3 + c ^ 3)) := by 
      field_simp 
      ring 
    rw [h7'] at *
    have h14 : 0 < (a + b) * (b + c) * (c + a) * (a ^ 3 + b ^ 3 + c ^ 3) := by positivity 
    have h18 : a * b * (b + c) * (c + a) * (a ^ 3 + b ^ 3 + c ^ 3) + b * c * (a + b) * (c + a) * (a ^ 3 + b ^ 3 + c ^ 3) + 
          c * a * (a + b) * (b + c) * (a ^ 3 + b ^ 3 + c ^ 3) - 
          (a + b + c) * (a + b) * (b + c) * (c + a) ≥ 0 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)), 
          sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)), 
          sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          mul_pos h21 h22, mul_pos h22 h23, mul_pos h21 h23, 
          sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (a^2 - c^2), 
          sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a), 
          habc, mul_pos h21 (show 0 < a ^ 3 + b ^ 3 + c ^ 3 by positivity)
          ]
    apply div_nonneg
    linarith
    all_goals positivity
  linarith