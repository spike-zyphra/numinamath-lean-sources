import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

theorem inequalities_1730
  (a b c : ℝ)
  (ha : a ∈ Set.Icc 1 2)
  (hb : b ∈ Set.Icc 1 2)
  (hc : c ∈ Set.Icc 1 2) :
  a^2 + b^2 + c^2 + a * b + b * c + a * c + 3 * (a + b) * (b + c) * (c + a) ≥ (a + b + c)^3 := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2),
          mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1), 
          mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hc1), 
          mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hc1), 
          mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hb2), 
          mul_nonneg (sub_nonneg.mpr hb2) (sub_nonneg.mpr hc2), 
          mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hc2)
        ]