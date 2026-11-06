import Mathlib

/- Danica wants to arrange her model cars in rows with exactly 6 cars in each row. She now has 23 model cars. What is the greatest number of additional cars she must buy in order to be able to arrange all her cars this way?
(A) 3(B) 2(C) 1(D) 4(E) 533 -/
theorem number_theory_97660 (s : Set ℕ) (hs: s = {m : ℕ | (m + 23) % 6 = 0}) :
IsLeast (s) (1) := by
unfold IsLeast
constructor
--the element 1 is so that 23 + 1 % 6 = 0
· rw[hs]
  simp
--the element 1 is the lower bound of the set.
· unfold lowerBounds
  simp
  intro a ha
--by contraddiction if it were not to be the lower bound then 0 should be, but 0 is not in s
  by_contra k
  push_neg at k
  have haz: a = 0 := by exact Nat.lt_one_iff.mp k
  rw[haz, hs] at ha
  simp at ha