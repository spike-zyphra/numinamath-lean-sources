import Mathlib

open Real
open scoped BigOperators

theorem inequalities_293271 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) ≥ 0 ∧
  (a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) = 0 ↔
    (a = b ∧ b = c)) := by
  constructor
  · -- Prove the inequality: $a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) \geq 0$
    have h1 : 0 < a * b * c := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
      mul_pos (show 0 < a + b - c from by linarith) (show 0 < a + c - b from by linarith),
      mul_pos (show 0 < a + c - b from by linarith) (show 0 < b + c - a from by linarith),
      mul_pos (show 0 < a + b - c from by linarith) (show 0 < b + c - a from by linarith),
      sq_nonneg (a * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)),
      mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < a * c from mul_pos ha hc),
      mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < b * c from mul_pos hb hc),
      mul_pos (show 0 < a * c from mul_pos ha hc) (show 0 < b * c from mul_pos hb hc)
    ]
  · -- Prove the equality condition
    constructor
    · -- Assume the expression = 0, prove a = b ∧ b = c
      intro heq
      have h1 : (a - b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos (show 0 < a + b - c from by linarith) (show 0 < a + c - b from by linarith),
          mul_pos (show 0 < a + c - b from by linarith) (show 0 < b + c - a from by linarith),
          mul_pos (show 0 < a + b - c from by linarith) (show 0 < b + c - a from by linarith),
          sq_nonneg (a * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)),
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith),
          mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith),
          mul_nonneg (show 0 ≤ c by linarith) (show 0 ≤ a by linarith)]
      have h2 : (b - c) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos (show 0 < a + b - c from by linarith) (show 0 < a + c - b from by linarith),
          mul_pos (show 0 < a + c - b from by linarith) (show 0 < b + c - a from by linarith),
          mul_pos (show 0 < a + b - c from by linarith) (show 0 < b + c - a from by linarith),
          sq_nonneg (a * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)),
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith),
          mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith),
          mul_nonneg (show 0 ≤ c by linarith) (show 0 ≤ a by linarith)]
      have ha1 : a - b = 0 := by
        nlinarith
      have hb1 : b - c = 0 := by
        nlinarith
      have h3 : a = b := by
        linarith
      have h4 : b = c := by
        linarith
      exact ⟨h3, h4⟩
    · -- Assume a = b ∧ b = c, prove the expression = 0
      rintro ⟨ha1, hb1⟩
      have h1 : a = b := ha1
      have h2 : b = c := hb1
      have h3 : a = c := by linarith [ha1, hb1]
      rw [show b = a by linarith [h1]] 
      rw [show c = a by linarith [h3]]
      nlinarith