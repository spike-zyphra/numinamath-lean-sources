import Mathlib

theorem inequalities_245509 (a b c : ℝ) (ha : -1 < a ∧ a < 1) (hb : -1 < b ∧ b < 1) (hc : -1 < c ∧ c < 1) :
    a * b * c + 2 > a + b + c := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  nlinarith [mul_pos (sub_pos.mpr ha2) (sub_pos.mpr hb2), -- (1 - a)(1 - b)
          mul_pos (sub_pos.mpr ha2) (sub_pos.mpr hc2), -- (1 - a)(1 - c)
          mul_pos (sub_pos.mpr hb2) (sub_pos.mpr hc2), -- (1 - b)(1 - c)
          mul_pos (sub_pos.mpr ha1) (sub_pos.mpr hb1), -- (a + 1)(b + 1)
          mul_pos (sub_pos.mpr ha1) (sub_pos.mpr hc1), -- (a + 1)(c + 1)
          mul_pos (sub_pos.mpr hb1) (sub_pos.mpr hc1), -- (b + 1)(c + 1)
          mul_pos (mul_pos (sub_pos.mpr ha1) (sub_pos.mpr hb1)) (sub_pos.mpr hc1), -- (a + 1)(b + 1)(c + 1)
          mul_pos (sub_pos.mpr ha2) (sub_pos.mpr hb2), -- (1 - a)(1 - b)
          mul_pos (sub_pos.mpr ha2) (sub_pos.mpr hc2), -- (1 - a)(1 - c)
          mul_pos (sub_pos.mpr hb2) (sub_pos.mpr hc2) -- (1 - b)(1 - c)
        ]