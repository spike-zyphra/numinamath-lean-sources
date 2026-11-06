import Mathlib

theorem number_theory_181976 : ∃ (a : Fin 4 → Fin 4 → ℤ),
  List.ofFn (fun i ↦ ∏ j : Fin 4, a i j) ∪ List.ofFn (fun j ↦ ∏ i : Fin 4, a i j)
  = ({1, 5, 7, 2019, -1, -5, -7, -2019} : Multiset ℤ) := by
  use fun i j => match i, j with
    | 0, 0 => -1
    | 0, 1 => -1
    | 0, 2 => -1
    | 0, 3 => -1
    | 1, 0 => 1
    | 1, 1 => 5
    | 1, 2 => 1
    | 1, 3 => 1
    | 2, 0 => 1
    | 2, 1 => 1
    | 2, 2 => 7
    | 2, 3 => 1
    | 3, 0 => 1
    | 3, 1 => 1
    | 3, 2 => 1
    | 3, 3 => 2019
    | _, _ => 0 -- This case should be unreachable, but satisfies the type checker
  native_decide