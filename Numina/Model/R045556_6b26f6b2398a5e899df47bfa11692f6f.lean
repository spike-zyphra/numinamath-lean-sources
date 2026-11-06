import Mathlib

theorem inequalities_140458 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ≤ b ∧ b ≤ a) :
    (a^2 - b^2) / c + (c^2 - b^2) / a + (a^2 - c^2) / b ≥ 3 * a - 4 * b + c := by
  rcases h with ⟨h1, h2⟩
  have ha' : 0 < a := ha
  have hb' : 0 < b := hb
  have hc' : 0 < c := hc
  have h3 : (a^2 - b^2) / c + (c^2 - b^2) / a + (a^2 - c^2) / b - (3 * a - 4 * b + c) ≥ 0 := by
    have h_pos1 : 0 < a * b * c := by
      positivity
    have h4 : (a^2 - b^2) / c + (c^2 - b^2) / a + (a^2 - c^2) / b - (3 * a - 4 * b + c) = 
      ((a ^ 2 - b ^ 2) * (a * b) + (c ^ 2 - b ^ 2) * (b * c) + (a ^ 2 - c ^ 2) * (a * c) - (3 * a - 4 * b + c) * (a * b * c)) / (a * b * c) := by
      field_simp
      ring
    rw [h4] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (b - c)), sq_nonneg (a * (a - c)), 
      sq_nonneg (b * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (b * (a - c)), 
      sq_nonneg (c * (a - b)), sq_nonneg (c * (b - c)), sq_nonneg (c * (a - c)), 
      mul_nonneg (show 0 ≤ c by linarith) (show 0 ≤ b - c by linarith), 
      mul_nonneg (show 0 ≤ b - c by linarith) (show 0 ≤ a - b by linarith), 
      mul_nonneg (show 0 ≤ c by linarith) (show 0 ≤ a - b by linarith), 
      mul_nonneg (show 0 ≤ (a - b : ℝ) by linarith) (show 0 ≤ (b - c : ℝ) by linarith), 
      mul_nonneg (show 0 ≤ (b - c : ℝ) by linarith) (show 0 ≤ (c : ℝ) by linarith)
    ]
    all_goals 
      positivity
  linarith