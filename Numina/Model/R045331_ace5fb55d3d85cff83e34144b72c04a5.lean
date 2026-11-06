import Mathlib

theorem algebra_93550 (b1 b1' b2 b2' b3 b3' : ℕ)
    (h1 : b1 + b1' = 26) (h2 : b2 + b2' = 28) (h3 : b3 + b3' = 30)
    (h1' : 2 * b1 = b1 + b1') (h2' : 4 * b2 = b2 + b2') (h3' : 5 * b3 = b3 + b3') :
  42 * (b1 + b2 + b3) = 13 * (b1 + b1' + b2 + b2' + b3 + b3') := by
  have eq1 : b1 = 13 := by
    omega
  have eq2 : b2 = 7 := by
    omega
  have eq3 : b3 = 6 := by
    omega
  have total_eq : b1 + b1' + b2 + b2' + b3 + b3' = 84 := by
    omega
  have total_yellow : b1 + b2 + b3 = 26 := by
    omega
  calc
    42 * (b1 + b2 + b3) = 42 * 26 := by rw [total_yellow]
    _ = 1092 := by norm_num
    _ = 13 * 84 := by norm_num
    _ = 13 * (b1 + b1' + b2 + b2' + b3 + b3') := by rw [total_eq]