import Mathlib

open Real

theorem inequalities_2611
    (a b : ℝ)
    (ha : 1 / 2 ≤ a ∧ a ≤ 3)
    (hb : 6 ≤ b ∧ b ≤ 63) :
    b / a ≤ 126 := by

  have ha1 : 1 / 2 ≤ a := ha.1
  have ha2 : a ≤ 3 := ha.2
  have hb1 : 6 ≤ b := hb.1
  have hb2 : b ≤ 63 := hb.2
  
  apply (div_le_iff₀ (by linarith)).mpr
  nlinarith