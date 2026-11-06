import Mathlib

theorem negated_inequalities_46595 (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    (a ^ 2 + a * c + c ^ 2) * (1 / (a + b + c) + 1 / (a + c)) + b ^ 2 * (1 / (b + c) + 1 / (a + b)) > a + b + c := by 
  have pos1 : 0 < a + b + c := by linarith
  have pos2 : 0 < a + c := by linarith
  have pos3 : 0 < b + c := by linarith
  have pos4 : 0 < a + b := by linarith
  have pos5 : a + b + c ≠ 0 := by linarith
  have pos6 : a + c ≠ 0 := by linarith
  have pos7 : b + c ≠ 0 := by linarith
  have pos8 : a + b ≠ 0 := by linarith
  have h9 : (a ^ 2 + a * c + c ^ 2) * (1 / (a + b + c) + 1 / (a + c)) + b ^ 2 * (1 / (b + c) + 1 / (a + b)) - (a + b + c) > 0 := by 
    have h10 : 0 < (a + b + c) * (a + c) * (b + c) * (a + b) := by positivity 
    have h11 : (a ^ 2 + a * c + c ^ 2) * (1 / (a + b + c) + 1 / (a + c)) + b ^ 2 * (1 / (b + c) + 1 / (a + b)) - (a + b + c) = 
      ((a ^ 2 + a * c + c ^ 2) * (2 * a + b + 2 * c) * (b + c) * (a + b) + b ^ 2 * (a + 2 * b + c) * (a + b + c) * (a + c) - (a + b + c) * ((a + b + c) * (a + c) * (b + c) * (a + b))) / ((a + b + c) * (a + c) * (b + c) * (a + b)) := by 
      field_simp 
      <;> ring 
    rw [h11]
    apply div_pos 
    · 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
        sq_nonneg (a * b - b * c), sq_nonneg (b * c - a * b), sq_nonneg (a * c - b * c), 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
        mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith), 
        mul_pos (show 0 < a * c by nlinarith) (show 0 < b * c by nlinarith)
        ]
    · 
      positivity 
  linarith