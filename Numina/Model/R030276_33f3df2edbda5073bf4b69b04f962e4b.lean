import Mathlib

open Real

theorem inequalities_228358 (k : ℝ) :
    IsLeast {x | 0 < x ∧ ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c →
      (a * b / (a + b + 2 * c) + b * c / (b + c + 2 * a) +
       c * a / (c + a + 2 * b)) ≤ x * (a + b + c)} (1 / 4) := by
  constructor
  · -- Show $1/4$ is in the set
    constructor
    · -- Show $1/4 > 0$
      norm_num
    · -- Show the inequality holds for all $a, b, c > 0$
      intro a b c ha hb hc
      have h3 : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
      have h1 : a * b / (a + b + 2 * c) + b * c / (b + c + 2 * a) + c * a / (c + a + 2 * b) ≤ (1 / 4) * (a + b + c) := by
        have pos1 : 0 < a + b + 2 * c := by positivity
        have pos2 : 0 < b + c + 2 * a := by positivity
        have pos3 : 0 < c + a + 2 * b := by positivity
        have h6 : a * b / (a + b + 2 * c) + b * c / (b + c + 2 * a) + c * a / (c + a + 2 * b) - (1 / 4) * (a + b + c) ≤ 0 := by
          have h7 : a * b / (a + b + 2 * c) + b * c / (b + c + 2 * a) + c * a / (c + a + 2 * b) - (1 / 4) * (a + b + c) =
              ( (a * b * (b + c + 2 * a) * (c + a + 2 * b) ) +
                (b * c * (a + b + 2 * c) * (c + a + 2 * b) ) +
                (c * a * (a + b + 2 * c) * (b + c + 2 * a) ) -
                (1 / 4) * (a + b + c) * (a + b + 2 * c) * (b + c + 2 * a) * (c + a + 2 * b) ) / ( (a + b + 2 * c) * (b + c + 2 * a) * (c + a + 2 * b) ) := by
            field_simp
            <;> ring
          rw [h7] at *
          apply div_nonpos_of_nonpos_of_nonneg
          · -- Show the numerator is ≤ 0
            have h8 : (a * b * (b + c + 2 * a) * (c + a + 2 * b) ) +
                (b * c * (a + b + 2 * c) * (c + a + 2 * b) ) +
                (c * a * (a + b + 2 * c) * (b + c + 2 * a) ) -
                (1 / 4) * (a + b + c) * (a + b + 2 * c) * (b + c + 2 * a) * (c + a + 2 * b) ≤ 0 := by
              nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
                  sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)),
                  sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)),
                  sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)), sq_nonneg (c * (a - b)),
                  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
                  mul_pos (mul_pos ha hb) hc, sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
                  mul_pos (show 0 < a * b by nlinarith) (show 0 < c by linarith)
                  ]
            linarith
          · -- Show the denominator is ≥ 0
            positivity
        linarith
      linarith
  · -- Show $1/4$ is the smallest
    intro x h
    rcases h with ⟨hx, h⟩
    have h1 := h 1 1 1 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h1 ⊢
    linarith