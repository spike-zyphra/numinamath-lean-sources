import Mathlib

/- The matrix
\[\begin{pmatrix} -\frac{7}{25} & \frac{24}{25} \\ \frac{24}{25} & \frac{7}{25} \end{pmatrix}\]corresponds to reflecting over a certain vector $\begin{pmatrix} x \\ y \end{pmatrix}.$  Find $\frac{y}{x}.$ -/
theorem calculus_22129 {x y : ℝ} (hx : x ≠ 0) (h : !![-7/25, 24/25; 24/25, 7/25].mulVecᵣ ![x, y] = ![x, y]) : y / x = 4 / 3 := by
  -- $x(-7 / 25) + y(24 / 25) = x$, so $y / x = 4 / 3$
  have eq1 : !![-7 / 25, 24 / 25; 24 / 25, 7 / 25].mulVecᵣ ![x, y] 0 = ![x, y] 0 := by
    rw [h]
  simp only [Fin.isValue, Matrix.mulVecᵣ_eq, Matrix.mulVec_cons, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.mulVec_empty, add_zero, Pi.add_apply, Pi.smul_apply, Function.comp_apply, Matrix.cons_val_zero, Matrix.head_cons, smul_eq_mul, Matrix.tail_cons] at eq1
  have : y = 4 / 3 * x := by
    linarith
  field_simp [this]
  ring