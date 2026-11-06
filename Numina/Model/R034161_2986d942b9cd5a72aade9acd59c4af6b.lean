import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_196581 (a b c d : ℝ) (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
  (hc : c ∈ Icc 0 1) (hd : d ∈ Icc 0 1) :
  (a + b + c + d + 1)^2 ≥ 4 * (a^2 + b^2 + c^2 + d^2) := by
  rcases ha with ⟨ha0, ha1⟩
  rcases hb with ⟨hb0, hb1⟩
  rcases hc with ⟨hc0, hc1⟩
  rcases hd with ⟨hd0, hd1⟩
  nlinarith [sq_nonneg (a + b + c + d - 1),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
          sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
          mul_nonneg (sub_nonneg.mpr ha0) (sub_nonneg.mpr ha1),
          mul_nonneg (sub_nonneg.mpr hb0) (sub_nonneg.mpr hb1),
          mul_nonneg (sub_nonneg.mpr hc0) (sub_nonneg.mpr hc1),
          mul_nonneg (sub_nonneg.mpr hd0) (sub_nonneg.mpr hd1)
        ]