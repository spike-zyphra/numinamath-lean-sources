import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_299096 {α β : ℝ} :
  Matrix.det (fun i j : Fin 3 => if i = j then 1 else if i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 0 then cos α else if i = 0 ∧ j = 2 ∨ i = 2 ∧ j = 0 then cos β else if i = 1 ∧ j = 2 ∨ i = 2 ∧ j = 1 then cos (α + β) else 0) = 0 := by 
  simp [Matrix.det_fin_three, Fin.sum_univ_three, Fin.sum_univ_two, add_assoc]
  <;> simp [cos_add]
  <;> ring_nf
  <;> simp [cos_sq, sin_sq]
  <;> ring