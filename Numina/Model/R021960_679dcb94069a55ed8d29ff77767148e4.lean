import Mathlib

theorem inequalities_44803
    (a b c d : ℝ)
    (ha : 0 < a ∧ a < 1)
    (hb : 0 < b ∧ b < 1)
    (hc : 0 < c ∧ c < 1)
    (hd : 0 < d ∧ d < 1) :
    1 + a * b + b * c + c * d + d * a + a * c + b * d > a + b + c + d := by
  rcases ha with ⟨ha0, ha1⟩
  rcases hb with ⟨hb0, hb1⟩
  rcases hc with ⟨hc0, hc1⟩
  rcases hd with ⟨hd0, hd1⟩
  nlinarith [mul_pos ha0 hb0, mul_pos ha0 hc0, mul_pos ha0 hd0, 
          mul_pos hb0 hc0, mul_pos hb0 hd0, mul_pos hc0 hd0, 
          mul_pos (sub_pos.mpr ha1) (sub_pos.mpr hb1), 
          mul_pos (sub_pos.mpr ha1) (sub_pos.mpr hc1), 
          mul_pos (sub_pos.mpr ha1) (sub_pos.mpr hd1), 
          mul_pos (sub_pos.mpr hb1) (sub_pos.mpr hc1), 
          mul_pos (sub_pos.mpr hb1) (sub_pos.mpr hd1), 
          mul_pos (sub_pos.mpr hc1) (sub_pos.mpr hd1)
        ]