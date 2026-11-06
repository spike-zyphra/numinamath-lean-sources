import Mathlib

theorem inequalities_602637 (a b c : Fin 2 → ℝ)
    (ha : 0 < a 0 * a 1)
    (hb : a 0 * c 0 ≥ b 0 ^ 2)
    (hc : a 1 * c 1 ≥ b 1 ^ 2) :
    (a 0 + a 1) * (c 0 + c 1) ≥ (b 0 + b 1) ^ 2 := by
  have h3 : a 0 * a 1 > 0 := ha
  have h7 : (a 0 * c 0 - b 0 ^ 2) + (a 1 * c 1 - b 1 ^ 2) ≥ 0 := by
    nlinarith
  have h8 : (a 0 * c 1 + a 1 * c 0) ≥ 2 * (b 0 * b 1) := by
    have h10 : (a 0) ^ 2 * (b 1) ^ 2 + (a 1) ^ 2 * (b 0) ^ 2 ≥ 2 * (a 0 * a 1 * (b 0 * b 1)) := by
      have h20 : (a 0 * b 1 - a 1 * b 0) ^ 2 ≥ 0 := by
        apply sq_nonneg
      nlinarith
    -- Now need to show from h10
    -- ` (a 0) ^ 2 * (b 1) ^ 2 + (a 1) ^ 2 * (b 0) ^ 2 ≥ 2 * (a 0 * a 1 * (b 0 * b 1)) ` that
    -- ` a 0 * c 1 + a 1 * c 0 ≥ 2 * (b 0 * b 1) `.
    nlinarith [sq_nonneg (a 0 * b 1 - a 1 * b 0), sq_nonneg (a 0 - a 1), sq_nonneg (c 0 - c 1), sq_nonneg (b 0 - b 1),
          sq_nonneg (a 0 * c 1 - a 1 * c 0), sq_nonneg (a 0 * b 1 - a 1 * b 0), sq_nonneg (b 0 * b 1), sq_nonneg (a 0 * a 1)]
  nlinarith