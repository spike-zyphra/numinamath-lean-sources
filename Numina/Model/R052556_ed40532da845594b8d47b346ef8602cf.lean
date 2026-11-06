import Mathlib

open Real

theorem algebra_176096 {h : ℝ} {d1 d2 : ℝ} (hh : h = 10) (hd1 : d1 = 20) (hd2 : d2 = 14)
    (V V' : ℝ) (hV : V = π * h / 12 * (d1 ^ 2 + d1 * d2 + d2 ^ 2)) (hV' : V' = π * h / 4 * ((d1 + d2) / 2) ^ 2)
    (hV'' : V'' = V - V') :
    V'' / V = 3 / 292 := by 
  subst hh
  subst hd1
  subst hd2
  subst hV
  subst hV'
  subst hV''
  field_simp
  ring_nf
  <;> linarith [Real.pi_pos]