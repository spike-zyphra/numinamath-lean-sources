import Mathlib

/- The average (mean) of 20 numbers is 30, and the average of 30 other numbers is 20.
What is the average of all 50 numbers?
(A) 23(B) 24(C) 25(D) 26(E) 27 -/

theorem algebra_95772 (a : Fin 20 → ℝ) (b : Fin 30 → ℝ) (ha : ∑ i : Fin 20, a i = 600)
(hb : ∑ i : Fin 30, b i = 600) :
((∑ i : Fin 20, a i) + (∑ i : Fin 30, b i)) / 50 = 24 := by 
--The claim follows by substitution of ha and hb and arithmetic
  rw[ha, hb]
  linarith