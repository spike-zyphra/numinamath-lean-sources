import Mathlib

theorem calculus_16233 (a b : EuclideanSpace ℝ (Fin 3))
    (ha : a = ![ -7, 0, 1]) (hb : b = ![ 4, 2, -1]) :
    a - 3 • b = ![ -19, -6, 4] := by
  rw [ha, hb]
  funext i
  fin_cases i <;> simp [Fin.sum_univ_three, sub_eq_add_neg, mul_add, add_mul]
  <;> norm_num