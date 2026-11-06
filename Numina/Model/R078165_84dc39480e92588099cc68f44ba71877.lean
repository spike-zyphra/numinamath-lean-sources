import Mathlib

theorem algebra_4925 {α β : ℝ} (hα : α^2-8*α+9=0) (hβ : β^2-8*β+9=0) (hαβ : α≠β) :
(α^2*β^3+α^3*β^2)/2=324 := by
  have h1 : α + β = 8 := by
    have h2 : α^2 - β^2 = 8 * (α - β) := by
      nlinarith [hα, hβ]
    have h3 : α - β ≠ 0 := by
      exact sub_ne_zero.mpr hαβ
    have h4 : (α + β) = 8 := by
      have h5 : (α - β) * (α + β - 8) = 0 := by
        nlinarith [h2]
      cases' (mul_eq_zero.1 h5) with h6 h7
      · 
        contradiction
      · 
        linarith
    linarith

  have h2 : α * β = 9 := by
    nlinarith [sq_pos_of_ne_zero (show α - β ≠ 0 by
      exact sub_ne_zero.mpr hαβ), sq_nonneg (α - β), h1]

  have h3 : α^2 * β^3 + α^3 * β^2 = (α * β)^2 * (α + β) := by
    ring

  rw [h3, h1, h2]
  all_goals linarith