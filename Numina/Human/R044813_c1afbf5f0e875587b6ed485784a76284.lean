import Mathlib

/- 29. The cells of a $4 \times 4$ table are filled with integers. In each row and each column, the product of all numbers is calculated. Could the resulting numbers be $1,5,7,2019,-1,-5,-7,-2019$ in some order? -/
theorem number_theory_181976 : ∃ (a : Fin 4 → Fin 4 → ℤ),
  List.ofFn (fun i ↦ ∏ j : Fin 4, a i j) ∪ List.ofFn (fun j ↦ ∏ i : Fin 4, a i j)
  = ({1, 5, 7, 2019, -1, -5, -7, -2019} : Multiset ℤ) := by
  -- provide a possible solution
  use ![
    ![-1, 1, 1, 1],
    ![1, -5, 1, 1],
    ![1, 1, -7, 1],
    ![-1, -1, -1, -2019]
  ]
  -- check it works
  decide