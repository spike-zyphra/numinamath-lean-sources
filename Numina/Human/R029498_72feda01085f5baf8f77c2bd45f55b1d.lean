import Mathlib

theorem inequalities_598175 (a b c : ℝ) (ha : a ∈ Set.Ioo (-1) 1) (hb : b ∈ Set.Ioo (-1) 1) (hc : c ∈ Set.Ioo (-1) 1) :
    a * b * c + 2 > a + b + c := by 
  have ha1 : -1 < a := ha.left
  have ha2 : a < 1 := ha.right
  have hb1 : -1 < b := hb.left
  have hb2 : b < 1 := hb.right
  have hc1 : -1 < c := hc.left
  have hc2 : c < 1 := hc.right
  nlinarith [mul_pos (show 0 < 1 - a by linarith) (show 0 < 1 - b by linarith), mul_pos (show 0 < 1 - a by linarith) (show 0 < 1 - c by linarith), mul_pos (show 0 < 1 - b by linarith) (show 0 < 1 - c by linarith)]