import Mathlib

theorem inequalities_322434 (a b c : ℝ) (ha : a ∈ Set.Icc (1 / 2) 1) (hb : b ∈ Set.Icc (1 / 2) 1) (hc : c ∈ Set.Icc (1 / 2) 1) :
    b / a + a / b ≤ 5 / 2 ∧ (a * b + b * c) / (a ^ 2 + 2 * b ^ 2 + c ^ 2) ≥ 2 / 5 := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  constructor
  · -- Prove $\frac{b}{a} + \frac{a}{b} \leqslant \frac{5}{2}$.
    have h1 : 0 < a := by 
      linarith 
    have h2 : 0 < b := by 
      linarith 
    have h3 : b / a + a / b - 5 / 2 ≤ 0 := by
      have h4 : b / a + a / b - 5 / 2 = (2 * b ^ 2 + 2 * a ^ 2 - 5 * a * b) / (2 * a * b) := by
        field_simp 
        ring
      rw [h4] at *
      have h5 : (2 * b ^ 2 + 2 * a ^ 2 - 5 * a * b : ℝ) ≤ 0 := by 
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ b by linarith), 
          mul_nonneg (show (0: ℝ) ≤ 1 - a by linarith) (show (0 : ℝ) ≤ 1 - b by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ 1 - b by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ 1 - a by linarith) (show (0 : ℝ) ≤ b by linarith), 
          sq_nonneg (a - b), sq_nonneg (a - 2 * b), sq_nonneg (2 * a - b)
        ]
      have h6 : (2 * a * b : ℝ) > 0 := by 
        nlinarith 
      apply div_nonpos_of_nonpos_of_nonneg 
      linarith 
      all_goals 
        nlinarith 
    linarith 
  · -- Prove $\frac{a b + b c}{a ^ 2 + 2 * b ^ 2 + c ^ 2} \geqslant \frac{2}{5}$.
    have h4 : 0 < a ^ 2 + 2 * b ^ 2 + c ^ 2 := by 
      nlinarith 
    have h5 : (a * b + b * c) / (a ^ 2 + 2 * b ^ 2 + c ^ 2) ≥ 2 / 5 := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), 
          sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2), 
          mul_nonneg (show (0 : ℝ) ≤ a - 1 / 2 by linarith) (show (0 : ℝ) ≤ b - 1 / 2 by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ b - 1 / 2 by linarith) (show (0 : ℝ) ≤ c - 1 / 2 by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ 1 - a by linarith) (show (0 : ℝ) ≤ 1 - b by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ 1 - b by linarith) (show (0 : ℝ) ≤ 1 - c by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ 1 - b by linarith)
        ]
    linarith