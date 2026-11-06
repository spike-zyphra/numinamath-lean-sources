import Mathlib

theorem inequalities_602771 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c ≥ max (max (max (max (max ((a - b) ^ 2 * a) ((a - b) ^ 2 * b)) ((b - c) ^ 2 * b)) ((b - c) ^ 2 * c)) ((c - a) ^ 2 * c)) ((c - a) ^ 2 * a) := by

  have h1 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c ≥ (a - b) ^ 2 * a := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a + b + c - 2 * a), sq_nonneg (a + b + c - 2 * b), sq_nonneg (a + b + c - 2 * c),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
  have h2 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c ≥ (a - b) ^ 2 * b := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a + b + c - 2 * a), sq_nonneg (a + b + c - 2 * b), sq_nonneg (a + b + c - 2 * c),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
  have h3 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c ≥ (b - c) ^ 2 * b := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a + b + c - 2 * a), sq_nonneg (a + b + c - 2 * b), sq_nonneg (a + b + c - 2 * c),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
  have h4 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c ≥ (b - c) ^ 2 * c := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a + b + c - 2 * a), sq_nonneg (a + b + c - 2 * b), sq_nonneg (a + b + c - 2 * c),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
  have h5 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c ≥ (c - a) ^ 2 * c := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a + b + c - 2 * a), sq_nonneg (a + b + c - 2 * b), sq_nonneg (a + b + c - 2 * c),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
  have h6 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c ≥ (c - a) ^ 2 * a := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a + b + c - 2 * a), sq_nonneg (a + b + c - 2 * b), sq_nonneg (a + b + c - 2 * c),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
  simp [max_le_iff, h1, h2, h3, h4, h5, h6]