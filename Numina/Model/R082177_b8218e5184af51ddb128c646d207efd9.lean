import Mathlib

theorem inequalities_119487 (a b c d e : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (h1 : a + b ≤ 1) (h2 : b + c ≤ 1) (h3 : c + d ≤ 1) (h4 : d + e ≤ 1) :
    a + b + c + d + e ≤ 3 := by
  linarith