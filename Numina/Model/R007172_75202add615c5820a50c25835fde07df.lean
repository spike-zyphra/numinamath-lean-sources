import Mathlib

theorem calculus_17262 (x y : ℝ) (m : Matrix (Fin 3) (Fin 3) ℝ) (hm : m = !![1, x, y; 1, x + y, y; 1, x, x + y]) :
    m.det = x * y := by
  rw [hm]
  simp [Matrix.det_fin_three, Fin.sum_univ_three, Fin.sum_univ_two, mul_add, add_mul]
  <;> ring