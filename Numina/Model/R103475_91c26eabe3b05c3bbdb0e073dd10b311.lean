import Mathlib

theorem algebra_306647 (a b c : ℝ) :
    Matrix.det (fun i j : Fin 3 => if i = 0 ∧ j = 0 then a + b else if i = 0 ∧ j = 1 then c else if i = 0 ∧ j = 2 then c else if i = 1 ∧ j = 0 then a else if i = 1 ∧ j = 1 then b + c else if i = 1 ∧ j = 2 then a else if i = 2 ∧ j = 0 then b else if i = 2 ∧ j = 1 then b else c + a) = 4 * a * b * c := by 
  simp [Matrix.det_fin_three, Fin.sum_univ_three]
  <;> ring
  <;> simp
  <;> ring
  <;> simp
  <;> ring
  <;> simp
  <;> ring
  <;> simp
  <;> ring
  <;> simp
  <;> ring
  <;> simp
  <;> ring