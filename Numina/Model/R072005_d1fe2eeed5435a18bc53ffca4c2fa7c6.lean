import Mathlib

theorem algebra_10806 {A B C D E F : ℝ × ℝ}
    (hA : A = (0, 6)) (hB : B = (0, 0)) (hC : C = (8, 0))
    (hD : D = ((A.1 + B.1) / 2, (A.2 + B.2) / 2))
    (hE : E = ((B.1 + C.1) / 2, (B.2 + C.2) / 2))
    (hF : F = (8 / 3, 2)) :
    F.1 + F.2 = 14 / 3 := by
  rw [hF]
  norm_num