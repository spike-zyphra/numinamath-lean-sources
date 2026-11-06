import Mathlib

theorem algebra_97984
  {a b : ℝ}
  (h : 1 = (1 / 4) * 2 + a ∧ 2 = (1 / 4) * 1 + b)
  : a + b = 9 / 4 := by 
  rcases h with ⟨ha, hb⟩
  have ha2 : a = 1/2 := by
    linarith
  have hb2 : b = 7/4 := by
    linarith
  linarith [ha2, hb2]