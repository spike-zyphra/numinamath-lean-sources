import Mathlib

theorem algebra_138222 : Matrix.det (fun i j : Fin 3 => if (i = 0 ∧ j = 0) then 2 else if (i = 0 ∧ j = 1) then -1 else if (i = 0 ∧ j = 2) then 1 else if (i = 1 ∧ j = 0) then 3 else if (i = 1 ∧ j = 1) then 2 else if (i = 1 ∧ j = 2) then 2 else if (i = 2 ∧ j = 0) then 1 else if (i = 2 ∧ j = 1) then -2 else 1) = 5 := by
  native_decide