import Mathlib

open Finset


theorem inequalities_259835
    (a b : Fin 3 → ℝ)
    (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) :
    (a 0 * b 1 + a 1 * b 0 + a 1 * b 2 + a 2 * b 1 + a 2 * b 0 + a 0 * b 2)^2 ≥
    4 * (a 0 * a 1 + a 1 * a 2 + a 2 * a 0) * (b 0 * b 1 + b 1 * b 2 + b 2 * b 0) := by
  nlinarith [sq_nonneg (a 0 * b 1 - a 1 * b 0), sq_nonneg (a 0 * b 2 - a 2 * b 0), sq_nonneg (a 1 * b 2 - a 2 * b 1),
      sq_nonneg (a 0 * b 1 - a 1 * b 0 + a 0 * b 2 - a 2 * b 0 + a 1 * b 2 - a 2 * b 1), sq_nonneg (a 0 * b 1 - a 1 * b 0 - a 0 * b 2 + a 2 * b 0),
      sq_nonneg (a 0 * b 1 - a 1 * b 0 - a 1 * b 2 + a 2 * b 1), sq_nonneg (a 0 * b 2 - a 2 * b 0 - a 1 * b 2 + a 2 * b 1),
      mul_pos (ha 0) (hb 0), mul_pos (ha 0) (hb 1), mul_pos (ha 0) (hb 2),
      mul_pos (ha 1) (hb 0), mul_pos (ha 1) (hb 1), mul_pos (ha 1) (hb 2),
      mul_pos (ha 2) (hb 0), mul_pos (ha 2) (hb 1), mul_pos (ha 2) (hb 2)]