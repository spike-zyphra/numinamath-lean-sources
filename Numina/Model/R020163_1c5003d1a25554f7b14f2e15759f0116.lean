import Mathlib

theorem algebra_301611 (x : ℂ) :
    Matrix.det (fun i j : Fin 3 => if i = 0 ∧ j = 0 then -4 else if i = 0 ∧ j = 1 then 2 else if i = 0 ∧ j = 2 then -4 + 3 * .I else if i = 1 ∧ j = 0 then 3 else if i = 1 ∧ j = 1 then -5 else if i = 1 ∧ j = 2 then 2 - 5 * .I else if i = 2 ∧ j = 0 then -4 + 3 * .I else if i = 2 ∧ j = 1 then 2 - 5 * .I else if i = 2 ∧ j = 2 then x else 0) = 0 ↔ x = 1 + 5 * .I := by
  simp [Matrix.det_fin_three, Fin.sum_univ_succ, Fin.sum_univ_zero, mul_add, add_mul]
  constructor
  · -- Forward: if determinant is zero, then x = 1 + 5i
    intro h
    norm_num [Complex.ext_iff] at h ⊢
    constructor
    · -- Real part
      nlinarith
    · -- Imaginary part
      nlinarith
  · -- Backward: if x = 1 + 5i, then determinant is zero
    intro h
    rw [h]
    norm_num [Complex.ext_iff]