import Mathlib

theorem algebra_135705 (x p q r : Fin 3 → ℝ)
    (hx : x = ![3, -3, 4]) (hp : p = ![1, 0, 2])
    (hq : q = ![0, 1, 1]) (hr : r = ![2, -1, 4]) :
    x = p - 2 * q + r := by 
  funext i
  simp [hx, hp, hq, hr] <;> try {tauto} <;> 
  fin_cases i <;> simp [hx, hp, hq, hr, Fin.sum_univ_three] <;> 
  norm_num [Matrix.vecHead, Matrix.vecTail] <;> try {tauto}