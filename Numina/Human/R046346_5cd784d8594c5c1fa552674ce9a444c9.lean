import Mathlib

/- Solve for $x$ in
\[\begin{vmatrix} a + x & a - x & a - x \\ a - x & a + x & a - x \\ a - x & a - x & a + x \end{vmatrix} = 0.\]Give all possible values of $x,$ in terms of $a.$-/
theorem calculus_22605 (a x : ℝ) (V : Matrix (Fin 3) (Fin 3) ℝ) (hv : V = !![a + x, a - x, a - x;a - x, a + x, a - x; a - x, a - x, a + x]) :
    V.det = 0 ↔ x = 0 ∨ x = 3 * a := by
  have v00 : V 0 0 = a + x := by simp [hv]
  have v01 : V 0 1 = a - x := by simp [hv]
  have v02 : V 0 2 = a - x := by simp [hv]
  have v10 : V 1 0 = a - x := by simp [hv]
  have v11 : V 1 1 = a + x := by simp [hv]
  have v12 : V 1 2 = a - x := by simp [hv]
  have v20 : V 2 0 = a - x := by
    simp only [hv, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.vecCons_const, Matrix.cons_val_two,
      Nat.succ_eq_add_one, Nat.reduceAdd]
    convert Matrix.head_fin_const (a - x)
  have v21 : V 2 1 = a - x := by simp [hv]
  have v22 : V 2 2 = a + x := by simp [hv]
  --   We can expand the determinant as follows:
  -- \begin{align*}
  -- \begin{vmatrix} a + x & a - x & a - x \\ a - x & a + x & a - x \\ a - x & a - x & a + x \end{vmatrix} &= (a + x) \begin{vmatrix} a + x & a - x \\ a - x & a + x \end{vmatrix} - (a - x) \begin{vmatrix} a - x & a - x \\ a - x & a + x \end{vmatrix} + (a - x) \begin{vmatrix} a - x & a + x \\ a - x & a - x \end{vmatrix} \\
  -- &= (a + x)((a + x)^2 - (a - x)^2) \\
  -- &\quad - (a - x)((a - x)(a + x) - (a - x)(a - x)) + (a - x)((a - x)(a - x) - (a + x)(a - x)) \\
  -- &= (a + x)(4ax) - (a - x)^2 (2x) + (a - x)^2 (-2x) \\
  -- &= 12ax^2 - 4x^3 \\
  -- &= 4x^2 (3a - x).
  -- \end{align*}
  have vdet : V.det = 4 * x ^ 2 * (3 * a - x) := by
    rw [Matrix.det_fin_three, v00, v01, v02, v10, v11, v12, v20, v21, v22]
    ring
  constructor
  swap
  -- Verify that x=0,3a are solutions.
  . rw [vdet]
    rintro (rfl | rfl)
    all_goals norm_num
  -- Thus, the solutions in $x$ are $\boxed{0,3a}.$
  rw [vdet]
  intro hx
  rw [mul_eq_zero] at hx
  rcases hx with hx | hx
  . left
    simp at hx
    exact hx
  right
  linear_combination -hx
