import Mathlib

theorem algebra_136681 (A B C : EuclideanSpace ℝ (Fin 3))
    (hA : A = ![2, 2, 7]) (hB : B = ![0, 0, 6]) (hC : C = ![-2, 5, 7]) :
    let v1 := B - A
    let v2 := C - A
    let dotProduct := v1 0 * v2 0 + v1 1 * v2 1 + v1 2 * v2 2
    let cosθ := dotProduct / (norm v1 * norm v2)
    cosθ = 2 / 15 := by
  simp [hA, hB, hC]
  simp [Fin.sum_univ_three, inner, EuclideanSpace.norm_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  have h1 : √9 = 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h2 : √25 = 5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  norm_num [h1, h2]
  <;> ring_nf <;> norm_num