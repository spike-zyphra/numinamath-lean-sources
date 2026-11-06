import Mathlib

theorem inequalities_129990 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a * b * c = 1) (hrec : a + b + c > 1 / a + 1 / b + 1 / c) :
    (a > 1 ∧ b < 1 ∧ c < 1) ∨ (b > 1 ∧ a < 1 ∧ c < 1) ∨ (c > 1 ∧ a < 1 ∧ b < 1) := by
  have h1 : 1 / a = b * c := by
    have h2 : a * b * c = 1 := hsum
    field_simp
    nlinarith
  have h2 : 1 / b = a * c := by
    have h3 : a * b * c = 1 := hsum
    field_simp
    nlinarith
  have h3 : 1 / c = a * b := by
    have h4 : a * b * c = 1 := hsum
    field_simp
    nlinarith
  rw [h1, h2, h3] at hrec
  by_cases ha1 : a > 1
  · -- Assume a > 1
    have hb1 : b < 1 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
    have hc1 : c < 1 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
    left
    exact ⟨ha1, hb1, hc1⟩
  · -- Assume not a > 1
    by_cases hb1 : b > 1
    · -- Assume b > 1
      have ha1 : a < 1 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
      have hc1 : c < 1 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
          ]
      right
      left
      exact ⟨hb1, ha1, hc1⟩
    · -- Assume not b > 1
      have ha1 : a ≤ 1 := by linarith
      have hb1 : b ≤ 1 := by linarith
      have hc1 : c > 1 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
          ]
      have ha2 : a < 1 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
          ]
      have hb2 : b < 1 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
          ]
      right
      right
      exact ⟨hc1, ha2, hb2⟩