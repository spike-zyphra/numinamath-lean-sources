import Mathlib

open Real

/- Evaluate
\[\begin{vmatrix} y + 1 & y & y \\ y & y + 1 & y \\ y & y & y + 1 \end{vmatrix}.\] -/
theorem calculus_16339 (y : ℝ) :
    Matrix.det (fun i j : Fin 3 => if i = j then y + 1 else y) = 3 * y + 1 := by
  simp [Matrix.det_fin_three]
  ring