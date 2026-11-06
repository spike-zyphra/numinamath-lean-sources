import Mathlib

theorem algebra_227250 (h : ∃ h₁ r, 
    h₁ > 0 ∧ r > 0 ∧                   -- 高度和速率为正
    h₁ - r * 2 = 10 - r * 2 ∧          -- 2小时后水位相同
    h₁ = r * 5 ∧                       -- 第一个水箱5小时后空
    10 = r * 8) :                      -- 第二个水箱8小时后空
    h₁ = 12.5 := by
  rcases h with ⟨h₁, r, h₁_pos, r_pos, h_eq1, h_eq2, h_eq3⟩
  have h3 : h₁ = 10 := by
    omega
  have h4 : r * 5 = 10 := by 
    nlinarith [h_eq2, h3]
  have h5 : r * 8 = 10 := by
    omega
  have h6 : r > 0 := r_pos
  omega