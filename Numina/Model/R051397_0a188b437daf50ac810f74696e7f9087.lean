import Mathlib

open Matrix Finset

theorem calculus_23300 {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : A = !![11/15, 2/15, 2/3; 2/15, 14/15, -1/3; 2/3, -1/3, -2/3]) :
    ∃ n : Fin 3 → ℝ, n 0 > 0 ∧ n 0 = 2 ∧ n 1 = -1 ∧ n 2 = -5 := by 
  use λ i =>
    match i with
    | 0 => (2 : ℝ)
    | 1 => (-1 : ℝ)
    | 2 => (-5 : ℝ)
    | _ => 0
  constructor
  · norm_num 
  constructor
  · -- show that 2 = 2
    rfl
  constructor
  · -- show that -1 = -1
    rfl
  · -- show that -5 = -5
    rfl