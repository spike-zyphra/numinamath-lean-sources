import Mathlib

open Real

theorem inequalities_243666 (m : ℝ) :
    (∀ a b c : ℝ, a > 0 → b > 0 → c > 0 → a + b + c = 1 → m * (a^3 + b^3 + c^3) ≥
      6 * (a^2 + b^2 + c^2) + 1) ↔ m ≥ 27 := by
  constructor
  · -- Assume that the inequality holds for all positive a, b, c with a + b + c = 1, prove m ≥ 27.
    intro h
    have h1 := h (1 / 3) (1 / 3) (1 / 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    nlinarith [sq_nonneg (1 / 3 : ℝ), sq_nonneg (1 / 3 : ℝ), sq_nonneg (1 / 3 : ℝ)]
    all_goals linarith
  · -- Show that if m ≥ 27, then the inequality holds.
    intro hm a b c ha hb hc h1
    have h2 : m * (a^3 + b^3 + c^3) ≥ 6 * (a^2 + b^2 + c^2) + 1 := by
      have h3 : a + b + c = 1 := h1
      have h4 : m ≥ 27 := hm
      suffices 27 * (a^3 + b^3 + c^3) ≥ 6 * (a^2 + b^2 + c^2) + 1 by
        nlinarith
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), sq_nonneg (c - 1 / 3),
        h1, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
    linarith