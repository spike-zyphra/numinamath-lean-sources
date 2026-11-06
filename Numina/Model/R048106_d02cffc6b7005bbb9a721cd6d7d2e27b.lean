import Mathlib

theorem inequalities_289585 (a b c : ℝ) (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) :
    ¬(1/4 < (1 - a) * b ∧ 1/4 < (1 - b) * c ∧ 1/4 < (1 - c) * a) := by
  rintro ⟨h₁, h₂, h₃⟩
  nlinarith [mul_pos ha.1 hb.1, mul_pos hb.1 hc.1, mul_pos ha.1 hc.1,
          mul_pos (sub_pos.mpr ha.2) (sub_pos.mpr hb.2), 
          mul_pos (sub_pos.mpr hb.2) (sub_pos.mpr hc.2), 
          mul_pos (sub_pos.mpr ha.2) (sub_pos.mpr hc.2),
          sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2)
        ]