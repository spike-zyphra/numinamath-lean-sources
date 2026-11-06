import Mathlib

/- Which of the following numbers is the largest?
(A) .99(B) .9099(C) .9(D) .909(E) .9009 -/
theorem number_theory_97155 (s: Set ℚ) (hs: s = {0.99, 0.9099, 0.9, 0.909, 0.9009}) : 
IsGreatest s (0.99) := by
--The proof relies on the fact that the element 0.99 is the largest in the set of all the answers
  unfold IsGreatest
  constructor
--0.99 is in the set (tautological)
  · rw[hs]
    simp
--0.99 is the upper bound
  · unfold upperBounds
    rw[hs]
    simp
    norm_num