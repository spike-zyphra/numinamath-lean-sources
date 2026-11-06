import Mathlib

open Real

theorem inequalities_92342 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 * (a ^ 4 + b ^ 4 + c ^ 4) < (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ↔
    a < b + c ∧ b < a + c ∧ c < a + b := by
  constructor
  · -- Assume 2 * (a ^ 4 + b ^ 4 + c ^ 4) < (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 prove a < b + c ∧ b < a + c ∧ c < a + b
    intro h
    have h1 : a < b + c := by
      by_contra h1'
      push_neg at h1'
      have h1_nonneg : a ^ 2 >= (b + c) ^ 2 := by
        nlinarith [sq_nonneg (a - (b + c)), sq_nonneg (a ^ 2 - (b + c) ^ 2), 
                  mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ c by linarith),
                  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
                  ]
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                  sq_nonneg (a ^ 2 - (b + c) ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg ((b + c) ^ 2 - a ^ 2),
                  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
                  ]
    have h2 : b < a + c := by
      by_contra h2'
      push_neg at h2'
      have h2_nonneg : b ^ 2 >= (a + c) ^ 2 := by
        nlinarith [sq_nonneg (b - (a + c)), sq_nonneg (b ^ 2 - (a + c) ^ 2), 
                  mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ c by linarith),
                  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
                  ]
      nlinarith [sq_nonneg (b * a - a * c), sq_nonneg (a * c - c * b), sq_nonneg (c * b - b * a),
                  sq_nonneg (b ^ 2 - (a + c) ^ 2), sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg ((a + c) ^ 2 - b ^ 2),
                  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
                  ]
    have h3 : c < a + b := by
      by_contra h3'
      push_neg at h3'
      have h3_nonneg : c ^ 2 >= (a + b) ^ 2 := by
        nlinarith [sq_nonneg (c - (a + b)), sq_nonneg (c ^ 2 - (a + b) ^ 2), 
                  mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ b by linarith),
                  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
                  ]
      nlinarith [sq_nonneg (c * a - a * b), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a),
                  sq_nonneg (c ^ 2 - (a + b) ^ 2), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg ((a + b) ^ 2 - c ^ 2),
                  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
                  ]
    exact ⟨h1, h2, h3⟩
  · -- Assume a < b + c ∧ b < a + c ∧ c < a + b prove 2 * (a ^ 4 + b ^ 4 + c ^ 4) < (a ^ 2 + b ^ 2 + c ^ 2) ^ 2
    rintro ⟨h1, h2, h3⟩
    nlinarith [sq_nonneg (a - b - c), sq_nonneg (b - a - c), sq_nonneg (c - a - b),
                sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a), 
                sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
                mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
                mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2), 
                mul_pos (sub_pos.mpr h1) (sub_pos.mpr h3), 
                mul_pos (sub_pos.mpr h2) (sub_pos.mpr h3)]
  all_goals 
    nlinarith [sq_nonneg (a - b - c), sq_nonneg (b - a - c), sq_nonneg (c - a - b),
          sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a), 
          sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
          ]