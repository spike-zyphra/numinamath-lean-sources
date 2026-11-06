import Mathlib

theorem inequalities_202485 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^3 + b^3 + c^3 ≥ a^2 * b + b^2 * c + c^2 * a ∧
    (a^3 + b^3 + c^3 = a^2 * b + b^2 * c + c^2 * a ↔ a = b ∧ b = c) := by

  constructor
  · -- Prove that a^3 + b^3 + c^3 ≥ a^2 * b + b^2 * c + c^2 * a
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]
  · -- Prove that a^3 + b^3 + c^3 = a^2 * b + b^2 * c + c^2 * a ↔ a = b ∧ b = c
    constructor
    · -- Forward: equality implies a = b ∧ b = c
      intro heq
      have h1 : (a - b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, heq
        ]
      have h2 : (b - c) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, heq
          ]
      have h3 : a - b = 0 := by
        nlinarith [h1
        ]
      have h4 : b - c = 0 := by
        nlinarith [h2
        ]
      constructor
      · -- Show that a = b
        linarith
      · -- Show that b = c
        linarith
    · -- Backward: a = b ∧ b = c implies equality
      rintro ⟨rfl, rfl⟩
      all_goals
        nlinarith