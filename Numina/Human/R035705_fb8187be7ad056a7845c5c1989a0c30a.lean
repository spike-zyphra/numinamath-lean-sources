import Mathlib

/- Marie does three equally time-consuming tasks in a row without taking breaks. 
She begins the first task at 1:00 PM and finishes the second task at 2:40 PM. 
When does she finish the third task?
(A)3:10 PM(B)3:30 PM(C)4:00 PM(D)4:10 PM(E)4:30 PM -/
theorem algebra_96787 (s e one tot: ℝ) (hs : s = 1) (he : e = 2+40/60) 
(hone : one = (e-s) / 2 ) (htot: tot = 3 * one):
s + tot = 3+30/60 := by 
--In order to perform decimal operations on time formats we have to convert them into decimals dividing minutes by 60. Once we do so, the problem boils down to substitution of the hypotheses into the claim.
  rw[htot, hone, he, hs]
  ring