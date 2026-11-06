import Mathlib

theorem inequalities_1670
    (a b : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (h : a^2 + b^2 = 1) :
    a^3 * b^3 / ((1 + a^6) * (1 + b^6)) ≤ 8 / 81 := by
  have h1 : 0 < a * b := by
    nlinarith
  have pos1 : 0 < (1 + a^6) * (1 + b^6) := by
    positivity
  have h2 : a^3 * b^3 / ((1 + a^6) * (1 + b^6)) ≤ 8 / 81 := by
    have h3 : a^3 * b^3 ≤ (8 / 81) * ((1 + a^6) * (1 + b^6)) := by
      nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a - b), sq_nonneg (a * b - 1 / 2),
          sq_nonneg (a^3 - b^3), sq_nonneg (a^2 - 1 / 2), sq_nonneg (b^2 - 1 / 2),
          sq_nonneg (a * b^3 - b * a^3), sq_nonneg (a^2 * b^2 - 1 / 4), 
          sq_nonneg (a^4 - a^2 * b^2), sq_nonneg (b^4 - a^2 * b^2), 
          mul_pos ha hb, 
          mul_pos (show 0 < a^2 by nlinarith) (show 0 < b^2 by nlinarith)
        ]
    apply (div_le_iff₀ pos1).mpr
    linarith [h3]
  exact h2