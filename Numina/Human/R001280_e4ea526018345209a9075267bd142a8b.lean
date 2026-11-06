import Mathlib

/- Given that
\[\begin{vmatrix} a & b & c \\ d & e & f \\ g & h & i \end{vmatrix} = -7,\]find
\[\begin{vmatrix} a & b & c \\ 2d + 5g & 2e + 5h & 2f + 5i \\ -g & -h & -i \end{vmatrix}.\] -/
theorem calculus_22734 (a b c d e f g h i : ℝ)
    (h₀ : !![a, b, c; d, e, f; g, h, i].det = -7) :
    !![a, b, c; 2 * d + 5 * g, 2 * e + 5 * h, 2 * f + 5 * i; -g, -h, -i].det = 14 := by
  simp only [Matrix.det_fin_three, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons, Matrix.head_fin_const] at h₀
  simp only [Matrix.det_fin_three, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons, Matrix.head_fin_const, mul_neg, sub_neg_eq_add]
  have h₁ : -(a * (2 * e + 5 * h) * i) + a * (2 * f + 5 * i) * h + b * (2 * d + 5 * g) * i + -(b * (2 * f + 5 * i) * g) + -(c * (2 * d + 5 * g) * h) + c * (2 * e + 5 * h) * g - (-2 * (a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g)) = 0 := by
    ring
  -- Therefore, the value of the determinant is 14.
  apply eq_of_sub_eq_zero at h₁
  rw [h₁, h₀]
  ring