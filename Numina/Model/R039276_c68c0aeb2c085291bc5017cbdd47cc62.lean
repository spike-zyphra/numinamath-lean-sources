import Mathlib

open Real

theorem inequalities_267478 (a b c : ℝ) (ha : a ∈ Set.Ioo 0 1) (hb : b ∈ Set.Ioo 0 1) (hc : c ∈ Set.Ioo 0 1) :
    1 ≤ a + b + c + 2 * (a * b + b * c + c * a) + 3 * (1 - a) * (1 - b) * (1 - c) ∧
    a + b + c + 2 * (a * b + b * c + c * a) + 3 * (1 - a) * (1 - b) * (1 - c) ≤ 9 := by 
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  constructor
  · -- Prove that 1 ≤ a + b + c + 2 * (a * b + b * c + c * a) + 3 * (1 - a) * (1 - b) * (1 - c)
    nlinarith [mul_pos ha1 hb1, mul_pos ha1 hc1, mul_pos hb1 hc1, 
      mul_pos (sub_pos.mpr ha2) (sub_pos.mpr hb2), 
      mul_pos (sub_pos.mpr ha2) (sub_pos.mpr hc2), 
      mul_pos (sub_pos.mpr hb2) (sub_pos.mpr hc2), 
      mul_pos (mul_pos ha1 hb1) hc1, 
      mul_pos (mul_pos ha1 hc1) hb1, 
      mul_pos (mul_pos hb1 hc1) ha1, 
      mul_pos (mul_pos (sub_pos.mpr ha2) (sub_pos.mpr hb2)) (sub_pos.mpr hc2)
    ]
  · -- Prove that a + b + c + 2 * (a * b + b * c + c * a) + 3 * (1 - a) * (1 - b) * (1 - c) ≤ 9
    nlinarith [mul_pos ha1 hb1, mul_pos ha1 hc1, mul_pos hb1 hc1, 
      mul_pos (sub_pos.mpr ha2) (sub_pos.mpr hb2), 
      mul_pos (sub_pos.mpr ha2) (sub_pos.mpr hc2), 
      mul_pos (sub_pos.mpr hb2) (sub_pos.mpr hc2), 
      mul_pos (mul_pos ha1 hb1) hc1, 
      mul_pos (mul_pos ha1 hc1) hb1, 
      mul_pos (mul_pos hb1 hc1) ha1, 
      mul_pos (mul_pos (sub_pos.mpr ha2) (sub_pos.mpr hb2)) (sub_pos.mpr hc2)
    ]