import Mathlib

open Real Set
open scoped Matrix

theorem calculus_12224 (α β : ℝ) :
  Matrix.det (fun i j : Fin 3 => if i = j then 0 else
    if i = 0 ∧ j = 1 then sin α else
    if i = 0 ∧ j = 2 then -cos α else
    if i = 1 ∧ j = 0 then -sin α else
    if i = 1 ∧ j = 1 then 0 else
    if i = 1 ∧ j = 2 then sin β else
    if i = 2 ∧ j = 0 then cos α else
    if i = 2 ∧ j = 1 then -sin β else
    0) = 0 := by
  simp [Matrix.det_fin_three, Fin.sum_univ_three, mul_add, add_mul, mul_comm, mul_assoc]
  <;> ring