import Mathlib
open Real

theorem inequalities_600871 (a b c : ℝ) (h₀ : 0 ≤ c) (h₁ : c ≤ b) (h₂ : b ≤ a)
    (h₃ : a + b + c = 3) :
    a * b^2 + b * c^2 + c * a^2 ≤ 27 / 8 ∧
    (a * b^2 + b * c^2 + c * a^2 = 27 / 8 ↔ a = 3 / 2 ∧ b = 3 / 2 ∧ c = 0) := by
  have h4 : a ≥ b := by linarith
  have h5 : b ≥ c := by linarith 
  have h6 : a - b ≥ 0 := by linarith
  have h7 : b - c ≥ 0 := by linarith
  constructor
  · 
    nlinarith [sq_nonneg (a - 3 / 2), sq_nonneg (b - 3 / 2), sq_nonneg (c - 0), 
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c), 
      mul_nonneg (show (0 : ℝ) ≤ c by linarith) (show (0 : ℝ) ≤ b - c by linarith),
      mul_nonneg (show (0 : ℝ) ≤ b - c by linarith) (show (0 : ℝ) ≤ a - b by linarith)
    ]
  · -- Show that equality holds iff a = 3/2, b = 3/2, c = 0 
    constructor 
    · -- Assume equality holds, prove the three conditions 
      intro h 
      have h4 : c = 0 := by
        nlinarith [sq_nonneg (a - 3 / 2), sq_nonneg (b - 3 / 2), sq_nonneg (c - 0), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c), 
          h, h₃
        ]
      have ha : a = 3 / 2 := by
        nlinarith [sq_nonneg (a - 3 / 2), sq_nonneg (b - 3 / 2), sq_nonneg (c - 0), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c), 
          h, h₃, h4
        ]
      have hb : b = 3 / 2 := by
        nlinarith [sq_nonneg (a - 3 / 2), sq_nonneg (b - 3 / 2), sq_nonneg (c - 0), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c), 
          h, h₃, h4, ha
        ]
      constructor
      · 
        linarith 
      constructor 
      · 
        linarith 
      · 
        linarith
    · -- Assume the conditions, prove equality
      rintro ⟨ha, hb, hc⟩
      rw [ha, hb, hc]
      norm_num