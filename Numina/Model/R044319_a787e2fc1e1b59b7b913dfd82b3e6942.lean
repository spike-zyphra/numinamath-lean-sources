import Mathlib

theorem inequalities_224871 (p q : ℝ) (hp : p ∈ Set.Ioo 0 1) (hq : q ∈ Set.Ioo 0 1)
    (h : 0 < q ∧ q < p) : p + 3 * q < 1 + 4 * p * q := by
  rcases hp with ⟨hp1, hp2⟩
  rcases hq with ⟨hq1, hq2⟩
  have hp3 : 0 < p := hp1
  have hp4 : p < 1 := hp2
  have hq3 : 0 < q := hq1
  have hq4 : q < 1 := hq2
  have h1 : 0 < q := hq1
  have h2 : q < p := h.right
  nlinarith [mul_pos (sub_pos.mpr hp1) (sub_pos.mpr hq1), 
          mul_pos (sub_pos.mpr hp1) (sub_pos.mpr (show 0 < 1 - p by linarith)), 
          mul_pos (sub_pos.mpr (show 0 < 1 - p by linarith)) (sub_pos.mpr hq1), 
          mul_pos (sub_pos.mpr hq1) (sub_pos.mpr (show 0 < 1 - q by linarith)), 
          mul_pos (sub_pos.mpr hq1) (sub_pos.mpr (show 0 < 1 - q by linarith)), 
          sq_nonneg (p - 1 / 2), sq_nonneg (q - 1 / 2), 
          mul_pos (sub_pos.mpr hq1) (sub_pos.mpr (show 0 < p - q by linarith)), 
          mul_pos (sub_pos.mpr (show 0 < 1 - p by linarith)) (sub_pos.mpr (show 0 < 1 - q by linarith)), 
          mul_pos (sub_pos.mpr (show 0 < p - q by linarith)) (sub_pos.mpr (show 0 < 1 - p by linarith)), 
          mul_pos (sub_pos.mpr (show 0 < p - q by linarith)) (sub_pos.mpr (show 0 < 1 - q by linarith)), 
          hq1, hq2, hp1, hp2, h2]