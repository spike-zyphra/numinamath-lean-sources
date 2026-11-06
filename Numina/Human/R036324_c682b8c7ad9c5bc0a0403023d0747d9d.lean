import Mathlib

open Pointwise
/- Which digit of .12345, when changed to 9, gives the largest number?
(A) 1(B) 2(C) 3(D) 4(E) 5 -/
theorem number_theory_97338 (s u : Set ℚ) (hu : u={0.12345}) (hs : s={0.8, 0.07, 0.006, 0.0005, 0.00004}):
IsGreatest (s + u) (0.92345 : ℚ) := by
--it is proven that 0.92345 is the greatst number in the set of 0.12345 + all the possible increments
unfold IsGreatest
constructor
--0.92345 is in the set
· rw[hs, hu]
  simp
  norm_num
--0.92345 is the greatest number in the set, proven case by case.
· unfold upperBounds
  simp
  intro a ha
  rw[hs, hu] at ha
  simp at ha
--extract all five cases
  obtain hA|hB|hC|hD|hE := ha
--analize case 0.92345 ≥ 0.92345
  · have hhh : a = 0.8 + 0.12345 := by exact Eq.symm (add_eq_of_eq_add_neg (id (Eq.symm hA)))
    ring_nf at hhh
    rw[hhh]
    ring_nf
    linarith
--analize case 0.92345 ≥ 0.19345
  · have hhh : a = 0.07 + 0.12345 := by exact Eq.symm (add_eq_of_eq_add_neg (id (Eq.symm hB)))
    ring_nf at hhh
    rw[hhh]
    ring_nf
    linarith
--analize case 0.92345 ≥ 0.12945
  · have hhh : a = 0.006 + 0.12345 := by exact Eq.symm (add_eq_of_eq_add_neg (id (Eq.symm hC)))
    ring_nf at hhh
    rw[hhh]
    ring_nf
    linarith
--analize case 0.92345 ≥ 0.12395
  · have hhh : a = 0.0005 + 0.12345 := by exact Eq.symm (add_eq_of_eq_add_neg (id (Eq.symm hD)))
    ring_nf at hhh
    rw[hhh]
    ring_nf
    linarith
--analize case 0.92345 ≥ 0.12349
  · have hhh : a = 0.00004 + 0.12345 := by exact Eq.symm (add_eq_of_eq_add_neg (id (Eq.symm hE)))
    ring_nf at hhh
    rw[hhh]
    ring_nf
    linarith