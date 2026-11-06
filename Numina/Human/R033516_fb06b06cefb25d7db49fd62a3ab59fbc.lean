import Mathlib
open Real
/- Four positive integers are given. Select any three of these integers, find their arithmetic average, and add this result to the fourth integer. Thus the numbers 29, 23, 21, and 17 are obtained. One of the original integers is:
(A) 19 (B) 21 (C) 23 (D) 29 (E) 17
-/
theorem algebra_96012 (a b c d : ℕ)
  (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
  (h1 : (a + b + c:ℝ) / 3 + d = 29)
  (h2 : (a + b + d:ℝ) / 3 + c = 23)
  (h3 : (a + c + d:ℝ) / 3 + b = 21)
  (h4 : (b + c + d:ℝ) / 3 + a = 17)
: d = 21 := by
  -- getting rid of divisions
  field_simp at *
  -- Adding all of the equations together
  have h:(29:ℝ)*3+23*3+21*3+17*3=270:=by norm_num
  rw [← h1,← h2,← h3,← h4] at h
  -- some intermediate steps : treat (a+b+c) as a whole and eliminate it to get the value of d
  -- have h'   : 3*(a:ℝ)+3*b+3*c+3*d  = 135              := by linarith
  -- have h1'  : (a:ℝ)+b+c+3*d+48     = 3*a+3*b+3*c+3*d  := by linarith
  -- have h1'' : (a:ℝ)+b+c            = 24               := by linarith
  have h1'' : (d:ℝ)                = 21               := by linarith
  norm_cast at h1''