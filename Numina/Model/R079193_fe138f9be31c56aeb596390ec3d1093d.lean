import Mathlib

theorem algebra_1831
  {a : ℤ} (ha : Even a) (h : 4 * a = (a + 2) + (a + 4) + 6) :
  a = 6 := by 
  linarith