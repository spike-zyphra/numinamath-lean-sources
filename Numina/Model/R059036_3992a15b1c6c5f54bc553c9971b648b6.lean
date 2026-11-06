import Mathlib

theorem inequalities_325294 (a b c : ℝ) (ha : a ∈ Set.Ioo (-1) 1) (hb : b ∈ Set.Ioo (-1) 1)
    (hc : c ∈ Set.Ioo (-1) 1) :
    a * b * c + 2 > a + b + c := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos (sub_pos.mpr ha2) (sub_pos.mpr hb2), mul_pos (sub_pos.mpr hb2) (sub_pos.mpr hc2),
          mul_pos (sub_pos.mpr ha2) (sub_pos.mpr hc2),
          mul_pos (sub_pos.mpr (show a + 1 > 0 by linarith)) (sub_pos.mpr (show b + 1 > 0 by linarith)),
          mul_pos (sub_pos.mpr (show b + 1 > 0 by linarith)) (sub_pos.mpr (show c + 1 > 0 by linarith)),
          mul_pos (sub_pos.mpr (show a + 1 > 0 by linarith)) (sub_pos.mpr (show c + 1 > 0 by linarith))
          ]