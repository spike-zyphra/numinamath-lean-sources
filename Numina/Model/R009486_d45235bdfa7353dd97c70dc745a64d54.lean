import Mathlib

theorem algebra_96769 {U V W X Y Z : ℤ}
(hU : U = 2 * 2004 ^ 2005) (hV : V = 2004 ^ 2005) (hW : W = 2003 * 2004 ^ 2004)
(hX : X = 2 * 2004 ^ 2004) (hY : Y = 2004 ^ 2004) (hZ : Z = 2004 ^ 2003) :
U - V > V - W ∧ U - V > W - X ∧ U - V > X - Y ∧ U - V > Y - Z := by 
  rw [hU, hV, hW, hX, hY, hZ]
  norm_num