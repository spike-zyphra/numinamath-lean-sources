import Mathlib

theorem algebra_2631 (claudia claudia_brother : ℕ) (h1 : claudia = 4 * claudia_brother) (h2 : claudia + 1 = 3 * (claudia_brother + 1)) :
    ∃ n, claudia + n = 2 * (claudia_brother + n) := by
  have h3 : claudia_brother = 2 := by 
    linarith [h1, h2]
  have h4 : claudia = 8 := by 
    linarith [h1, h3]
  use 4
  linarith [h4, h3]