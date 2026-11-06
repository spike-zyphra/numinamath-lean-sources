import Mathlib

open Real
open scoped BigOperators

theorem inequalities_190036 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) :
  a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) ≥ 0 ∧
  (a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) = 0 ↔
    (a = b ∧ b = c)) := by
  constructor
  · -- Prove that $a^2 b(a-b) + b^2 c(b-c) + c^2 a(c-a) \geq 0$.
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
          mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), 
          mul_pos (sub_pos.mpr h'') (sub_pos.mpr h)
        ]
  · -- Prove the equality condition.
    constructor
    · -- Assume that the expression is zero, prove that a = b and b = c.
      intro heq
      have h1 : (a - b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
              mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
              mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), 
              mul_pos (sub_pos.mpr h'') (sub_pos.mpr h)
            ]
      have h2 : a - b = 0 := by
        rw [sq_eq_zero_iff] at h1
        linarith
      have h3 : a = b := by
        linarith
      have h4 : (b - c) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
              mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
              mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), 
              mul_pos (sub_pos.mpr h'') (sub_pos.mpr h)
            ]
      have h5 : b - c = 0 := by
        rw [sq_eq_zero_iff] at h4
        linarith
      have h6 : b = c := by
        linarith
      exact ⟨h3, h6⟩
    · -- Assume that a = b = c, prove that the expression is zero.
      rintro ⟨rfl, rfl⟩
      nlinarith [sq_nonneg (a * a - a * a), sq_nonneg (a * a - a * a), sq_nonneg (a * a - a * a), 
          sq_nonneg (a - a), sq_nonneg (a - a), sq_nonneg (a - a),
          mul_pos (show (0 : ℝ) < a by assumption) (show (0 : ℝ) < a by assumption)]