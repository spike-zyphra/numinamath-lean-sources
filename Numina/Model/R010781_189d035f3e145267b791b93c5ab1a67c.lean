import Mathlib

theorem algebra_15613 {A B C : ℝ × ℝ}
    (hA : A = (24, 7)) (hB : B = (3, 4))
    (hC : C = ((A.1 + B.1) / 2, (A.2 + B.2) / 2)) :
    2 * C.1 - 4 * C.2 = 5 := by 
  simp [hC, hA, hB]
  norm_num