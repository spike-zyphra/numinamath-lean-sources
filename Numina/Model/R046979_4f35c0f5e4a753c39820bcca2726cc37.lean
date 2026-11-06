import Mathlib

theorem inequalities_600041 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : a < b + c) (h2 : b < a + c) (h3 : c < a + b): 2 < (b + c) / a + (c + a) / b + (a + b) / c - (a^3 + b^3 + c^3) / (a * b * c) ∧ (b + c) / a + (c + a) / b + (a + b) / c - (a ^ 3 + b ^ 3 + c ^ 3) / (a * b * c) ≤ 3:= by
  constructor
  · -- First part: proving 2 < ... .
    have h15 : 2 < (b + c) / a + (c + a) / b + (a + b) / c - (a ^ 3 + b ^ 3 + c ^ 3) / (a * b * c) := by
      have h16 : 0 < a * b * c := by positivity
      have h8' : (b + c) / a + (c + a) / b + (a + b) / c - (a ^ 3 + b ^ 3 + c ^ 3) / (a * b * c) =
          ((b + c) * (b * c) + (c + a) * (a * c) + (a + b) * (a * b) - (a ^ 3 + b ^ 3 + c ^ 3)) / (a * b * c) := by
        field_simp [show a ≠ 0 by linarith, show b ≠ 0 by linarith, show c ≠ 0 by linarith]
        ring
      rw [h8'] at *
      apply (lt_div_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
        mul_pos (show 0 < c by linarith) (show 0 < a by linarith), 
        mul_pos (show 0 < c by linarith) (show 0 < b by linarith), 
        mul_pos (show 0 < b by linarith) (show 0 < a by linarith), 
        sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
        mul_pos (show 0 < b + c - a by linarith) (show 0 < a + c - b by linarith), 
        mul_pos (show 0 < b + c - a by linarith) (show 0 < a + b - c by linarith), 
        mul_pos (show 0 < a + c - b by linarith) (show 0 < a + b - c by linarith)
      ]
    exact h15
  · -- Second part: proving ... ≤ 3.
    have h7' : (b + c) / a + (c + a) / b + (a + b) / c - (a ^ 3 + b ^ 3 + c ^ 3) / (a * b * c) =
      ((b + c) * (b * c) + (c + a) * (a * c) + (a + b) * (a * b) - (a ^ 3 + b ^ 3 + c ^ 3)) / (a * b * c) := by
      field_simp [show a ≠ 0 by linarith, show b ≠ 0 by linarith, show c ≠ 0 by linarith]
      ring
    rw [h7'] at *
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
      sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
      mul_pos (show 0 < c by linarith) (show 0 < a by linarith), 
      mul_pos (show 0 < c by linarith) (show 0 < b by linarith), 
      mul_pos (show 0 < b by linarith) (show 0 < a by linarith), 
      mul_pos (show 0 < b + c - a by linarith) (show 0 < a + c - b by linarith), 
      mul_pos (show 0 < b + c - a by linarith) (show 0 < a + b - c by linarith), 
      mul_pos (show 0 < a + c - b by linarith) (show 0 < a + b - c by linarith)
    ]