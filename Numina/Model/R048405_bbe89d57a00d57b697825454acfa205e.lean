import Mathlib

theorem algebra_327378 (a b c d : ℝ) (P : ℝ → ℝ)
    (hP : P = fun x => x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d)
    (hP1 : P 1 = 7) (hP2 : P 2 = 52) (hP3 : P 3 = 97) :
    (P 9 + P (-5)) / 4 = 1202 := by
  rw [hP] at hP1 hP2 hP3
  simp at hP1 hP2 hP3 
  rw [hP]
  simp 
  linarith