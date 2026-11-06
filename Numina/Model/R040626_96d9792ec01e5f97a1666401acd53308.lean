import Mathlib

theorem calculus_22342 (i j k v : Fin 3 → ℝ) (hi : i = ![1, 0 ,0]) (hj : j = ![0, 1, 0])
    (hk : k = ![0, 0, 1]) (h : crossProduct i (crossProduct (v - j) i) +
    crossProduct j (crossProduct (v - k) j) + crossProduct k (crossProduct (v - i) k) = 0) :
    v = ![1 / 2, 1 / 2, 1 / 2] := by
  rw [hi, hj, hk] at h
  have eq1 := congr_arg (λ x => x 0) h
  have eq2 := congr_arg (λ x => x 1) h
  have eq3 := congr_arg (λ x => x 2) h
  simp [crossProduct, Fin.sum_univ_three, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons] at eq1 eq2 eq3 
  have h0 : v 0 = 1 / 2 := by linarith
  have h1 : v 1 = 1 / 2 := by linarith
  have h2 : v 2 = 1 / 2 := by linarith
  funext i
  fin_cases i 
  · exact h0 
  · exact h1 
  · exact h2