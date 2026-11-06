import Mathlib

theorem inequalities_8199 (a b c d : ℤ) (ha : a < 2 * b) (hb : b < 3 * c) (hc : c < 4 * d)
    (hd : d < 20) : a ≤ 447 := by
  have h1 : d ≤ 19 := by linarith
  have h2 : c ≤ 75 := by 
    linarith [hc, h1]
  have h3 : b ≤ 224 := by
    linarith [hb, h2]
  have h4 : a ≤ 447 := by
    linarith [ha, h3]
  linarith