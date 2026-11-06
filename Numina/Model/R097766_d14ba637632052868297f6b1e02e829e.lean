import Mathlib

theorem algebra_271312 (a b c d : ℝ) :
    Matrix.det (fun i j : Fin 3 => match i with
      | 0 => match j with
        | 0 => a^2 + b^2 - c^2 - d^2
        | 1 => 2 * b * c - 2 * a * d
        | 2 => 2 * b * d + 2 * a * c
      | 1 => match j with
        | 0 => 2 * b * c + 2 * a * d
        | 1 => a^2 - b^2 + c^2 - d^2
        | 2 => 2 * c * d - 2 * a * b
      | 2 => match j with
        | 0 => 2 * b * d - 2 * a * c
        | 1 => 2 * c * d + 2 * a * b
        | 2 => a^2 - b^2 - c^2 + d^2) = (a^2 + b^2 + c^2 + d^2)^3 := by 
  simp [Matrix.det_fin_three]
  ring