import Mathlib

theorem calculus_16637 (A B C D : EuclideanSpace ℝ (Fin 3))
    (hA : A = ![3, -1, 2]) (hB : B = ![1, 2, -4]) (hC : C = ![-1, 1, 2])
    (hD : D - A = C - B) :
    D = ![1, -2, 8] := by
  rw [hA] at hD
  rw [hB] at hD
  rw [hC] at hD

  have hD1 := congr_arg (fun v => v 0) hD
  have hD2 := congr_arg (fun v => v 1) hD
  have hD3 := congr_arg (fun v => v 2) hD
  simp [Fin.sum_univ_three] at hD1 hD2 hD3
  have hD0 : D 0 = 1 := by linarith 
  have hD1' : D 1 = -2 := by linarith 
  have hD2' : D 2 = 8 := by linarith 
  ext i
  fin_cases i 
  · exact hD0
  · exact hD1'
  · exact hD2'