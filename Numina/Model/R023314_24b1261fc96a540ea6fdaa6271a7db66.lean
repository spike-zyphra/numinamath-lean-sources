import Mathlib

theorem inequalities_162932 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    3 / 2 ≤ 1 / (a ^ 2 * (b + c)) + 1 / (b ^ 2 * (c + a)) + 1 / (c ^ 2 * (a + b)) := by 
  have pos1 : 0 < a * b * c := by
    positivity
  have h1 : a * b * c = 1 := habc
  
  have pos1 : 0 < a ^ 2 * (b + c) := by positivity
  have pos2 : 0 < b ^ 2 * (c + a) := by positivity
  have pos3 : 0 < c ^ 2 * (a + b) := by positivity
  
  have h3 : 1 / (a ^ 2 * (b + c)) + 1 / (b ^ 2 * (c + a)) + 1 / (c ^ 2 * (a + b)) - 3 / 2 ≥ 0 := by 
    have pos4 : 0 < a ^ 2 * (b + c) * b ^ 2 * (c + a) * c ^ 2 * (a + b) := by
      positivity
    have h4 : 1 / (a ^ 2 * (b + c)) + 1 / (b ^ 2 * (c + a)) + 1 / (c ^ 2 * (a + b)) - 3 / 2 =
        ( (b ^ 2 * c ^ 2 * (a + b) * (c + a)) + (a ^ 2 * c ^ 2 * (a + b) * (b + c)) + (a ^ 2 * b ^ 2 * (b + c) * (c + a)) - (3 / 2) * (a ^ 2 * b ^ 2 * c ^ 2 * (a + b) * (b + c) * (c + a)) ) / (a ^ 2 * (b + c) * b ^ 2 * (c + a) * c ^ 2 * (a + b)) := by 
      field_simp
      <;> ring_nf <;> field_simp
      <;> ring_nf
      <;> nlinarith
    rw [h4] at *
    apply div_nonneg
    have h6 : a * b * c = 1 := habc
    have h7 : a^2 * b^2 * c^2 = 1 := by 
      calc 
        a^2 * b ^2 * c ^2 = (a * b * c) ^ 2 := by ring
        _ = 1 ^2 := by rw [h6]
        _ = 1 := by norm_num
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith), mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), mul_pos (show 0 < a * c by nlinarith) (show 0 < b * c by nlinarith), habc, h7
    ]
    all_goals positivity
  linarith