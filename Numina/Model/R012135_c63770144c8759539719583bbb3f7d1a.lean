import Mathlib

theorem number_theory_87978 :
  (Nat.divisors 6000).card = 40 ∧ ((Nat.divisors 6000).filter (fun x => ¬IsSquare x)).card = 34 := by 
  constructor
  · -- Show that the cardinality of the divisors of 6000 is 40
    native_decide
  · -- Show that the cardinality of the divisors of 6000 which are not perfect squares is 34
    native_decide