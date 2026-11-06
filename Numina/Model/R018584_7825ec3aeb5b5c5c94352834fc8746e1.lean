import Mathlib

theorem algebra_71591 :
    ∃ x : Fin 3 → ℕ, (∀ i j, i ≠ j → x i ≠ x j) ∧
      ∏ c, (x c - x ((c + 1) % 3)) = ∏ c, (x c - x ((c + 2) % 3)) := by 
  use λ i => 
    match i with
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | _ => 0
  constructor
  · -- Show all elements are different
    intro i j h_ineq
    fin_cases i <;> fin_cases j <;> simp at *
    all_goals 
      omega 
  · -- Show the products are equal 
    native_decide