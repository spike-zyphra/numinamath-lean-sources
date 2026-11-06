import Mathlib

open Matrix

theorem algebra_175966 : Matrix.det (fun i j : Fin 4 => if (i = 0 ∧ j = 0) then 3 else if (i = 0 ∧ j = 1) then 1 else if (i = 0 ∧ j = 2) then -1 else if (i = 0 ∧ j = 3) then 2 else if (i = 1 ∧ j = 0) then -3 else if (i = 1 ∧ j = 1) then 1 else if (i = 1 ∧ j = 2) then 4 else if (i = 1 ∧ j = 3) then -5 else if (i = 2 ∧ j = 0) then 2 else if (i = 2 ∧ j = 1) then 0 else if (i = 2 ∧ j = 2) then 1 else if (i = 2 ∧ j = 3) then -1 else if (i = 3 ∧ j = 0) then 3 else if (i = 3 ∧ j = 1) then -5 else if (i = 3 ∧ j = 2) then 4 else -4) = 40 := by
  native_decide