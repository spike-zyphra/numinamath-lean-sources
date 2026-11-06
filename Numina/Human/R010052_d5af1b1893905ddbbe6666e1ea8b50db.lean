import Mathlib
open Real
/-Which of the following numbers has the smallest prime factor?
(A) 55 (B) 57 (C) 58 (D) 59  (E) 61-/
theorem number_theory_95293 :
(Nat.minFac 55 = 5 ∧ Nat.minFac 57 = 3 ∧ Nat.minFac 58 = 2 ∧ Nat.minFac 59 = 59 ∧ Nat.minFac 61 = 61) := by
  -- calculating the corresponding minimum factor of the options 
  reduce
  -- then we can obtain the answer
  simp