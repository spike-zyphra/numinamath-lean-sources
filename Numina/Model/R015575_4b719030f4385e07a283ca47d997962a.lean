import Mathlib

theorem other_143946 (h : ∃ x, x ∈ Set.Ioo 12 14 ∧ (x - 12) * 60 = (14 - x) * 12) :
    x = 12.401320 := by
  rcases h with ⟨x, hx_pos, heq⟩
  rcases hx_pos with ⟨hx1, hx2⟩
  have h3 : x = 13 := by 
    omega
  have h4 : (x - 12) * 60 = (14 - x) * 12 := by
    omega
  rw [show x = 13 by omega] at h4
  all_goals omega
  all_goals norm_num at h4
  all_goals omega