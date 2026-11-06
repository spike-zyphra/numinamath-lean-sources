import Mathlib

theorem other_164468 (d : ℝ) (h : d = 18030 - 17880) :
    d = 150 ∧ (10.5 / d) * 350 = 24.5 := by
  have hd : d = 150 := by
    rw [h]
    norm_num
  have h2 : (10.5 / d) * 350 = 24.5 := by
    rw [hd]
    norm_num
  exact ⟨hd, h2⟩