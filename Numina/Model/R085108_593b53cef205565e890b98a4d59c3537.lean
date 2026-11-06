import Mathlib

theorem algebra_105809 (A B C D E F G H : ℝ) (hC : C = 5) (hA : A + B + C = 30)
    (hB : B + C + D = 30) (hC' : C + D + E = 30) (hD : D + E + F = 30)
    (hE : E + F + G = 30) (hF : F + G + H = 30) :
    A + H = 25 := by 
  rw [hC] at hA hB hC'
  linarith