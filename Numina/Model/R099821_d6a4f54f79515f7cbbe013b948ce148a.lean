import Mathlib

theorem number_theory_142106 :
    ∑ n in (Finset.Icc 1000 9999).filter (fun n => IsSquare (n / 100) ∧ IsSquare ((n / 10) % 100) ∧ IsSquare (n % 100)), n = 13462 := by 
  native_decide