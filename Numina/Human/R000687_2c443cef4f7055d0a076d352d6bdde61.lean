import Mathlib

theorem algebra_904 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : 4 * (a + b) = 1) (h2 : 5 * (a + c) = 1) (h3 : 6 * (b + c) = 1) :
   a + b + c =  37 / 120 := by linarith --algebraic calculation that can be simply closed by linarith.