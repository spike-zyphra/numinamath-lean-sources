import Mathlib

open Real
open scoped BigOperators

theorem inequalities_246290 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    b^2 * c^2 + c^2 * a^2 + a^2 * b^2 > (1 / 2) * (a^4 + b^4 + c^4) ↔
    (a < b + c) ∧ (b < a + c) ∧ (c < a + b) := by
  constructor
  · -- Proof of the forward direction
    intro h
    have h1 : 2 * (b^2 * c^2 + c^2 * a^2 + a^2 * b^2) > a^4 + b^4 + c^4 := by
      linarith
    have h4 : (b + c - a) * (a + c - b) * (a + b - c) > 0 := by
      nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (mul_pos ha hb) hc
      ]
    constructor
    · -- Show a < b + c
      nlinarith [sq_nonneg (b + c - a), sq_nonneg (a + c - b), sq_nonneg (a + b - c),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
    constructor
    · -- Show b < a + c
      nlinarith [sq_nonneg (b + c - a), sq_nonneg (a + c - b), sq_nonneg (a + b - c),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
    · -- Show c < a + b
      nlinarith [sq_nonneg (b + c - a), sq_nonneg (a + c - b), sq_nonneg (a + b - c),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
  · -- Proof of the reverse direction
    rintro ⟨h1, h2, h3⟩
    have h4 : (b + c - a) * (a + c - b) * (a + b - c) > 0 := by
      have pos1 : b + c - a > 0 := by linarith
      have pos2 : a + c - b > 0 := by linarith
      have pos3 : a + b - c > 0 := by linarith
      positivity
    have h1 : 2 * (b^2 * c^2 + c^2 * a^2 + a^2 * b^2) > a^4 + b^4 + c^4 := by
      nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (mul_pos ha hb) hc
      ]
    linarith