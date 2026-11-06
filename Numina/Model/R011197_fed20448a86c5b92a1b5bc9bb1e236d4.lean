import Mathlib

theorem Inequalities_613610
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) + 1 / 3 ≥
    8 / 9 * (a / (b + c) + b / (c + a) + c / (a + b)) := by
  have pos1 : 0 < a * b + b * c + c * a := by
    positivity
  have pos2 : 0 < (b + c) * (c + a) * (a + b) := by
    positivity
  have h1 : (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) + 1 / 3 - 8 / 9 * (a / (b + c) + b / (c + a) + c / (a + b)) ≥ 0 := by
    -- Find a common denominator
    have hx_pos : 0 < (a * b + b * c + c * a) * (b + c) * (c + a) * (a + b) := by positivity
    have h2 : (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) + 1 / 3 - 8 / 9 * (a / (b + c) + b / (c + a) + c / (a + b)) = 
        ( (a ^ 2 + b ^ 2 + c ^ 2) * (b + c) * (c + a) * (a + b) + (1 / 3) * (a * b + b * c + c * a) * (b + c) * (c + a) * (a + b) - (8 / 9) * (a * (a * b + b * c + c * a) * (a + b) * (c + a) + b * (a * b + b * c + c * a) * (b + c) * (a + b) + c * (a * b + b * c + c * a) * (b + c) * (c + a)) ) / ((a * b + b * c + c * a) * (b + c) * (c + a) * (a + b)) := by 
      field_simp
      ring
    rw [h2] at *
    apply div_nonneg
    nlinarith [ 
      sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
      sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
      sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      mul_pos (show 0 < b + c by positivity) (show 0 < c + a by positivity), 
      mul_pos (show 0 < b + c by positivity) (show 0 < a + b by positivity), 
      mul_pos (show 0 < c + a by positivity) (show 0 < a + b by positivity)
    ]
    positivity
  linarith