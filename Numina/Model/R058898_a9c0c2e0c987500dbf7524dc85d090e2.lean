import Mathlib

theorem algebra_601832 {x y z : ℝ} (h1 : (x - 2)^2 + (y + 3 / 2)^2 + (z - 6)^2 = 64) (h2 : (x + 2)^2 + (y - 3 / 2)^2 + (z + 6)^2 = 25) :
    x = -6 / 13 ∧ y = 9 / 26 ∧ z = -18 / 13 := by

  have h3 : (x - -6 / 13) ^ 2 + (y - 9 / 26) ^ 2 + (z - -18 / 13) ^ 2 = 0 := by
    nlinarith
  
  have hx1 : x - -6 / 13 = 0 := by 
    nlinarith [sq_nonneg (x + 6 / 13), sq_nonneg (y - 9 / 26), sq_nonneg (z + 18 / 13)]

  have hy1 : y - 9 / 26 = 0 := by 
    nlinarith [sq_nonneg (x + 6 / 13), sq_nonneg (y - 9 / 26), sq_nonneg (z + 18 / 13)]

  have hz1 : z - -18 / 13 = 0 := by 
    nlinarith [sq_nonneg (x + 6 / 13), sq_nonneg (y - 9 / 26), sq_nonneg (z + 18 / 13)]

  have hx2 : x = -6 / 13 := by linarith

  have hy2 : y = 9 / 26 := by linarith

  have hz2 : z = -18 / 13 := by linarith

  exact ⟨hx2, hy2, hz2⟩