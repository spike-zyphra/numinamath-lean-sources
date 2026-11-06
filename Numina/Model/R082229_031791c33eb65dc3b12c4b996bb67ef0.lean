import Mathlib

theorem number_theory_145916 {P : ℕ} (hP : P = 3659893456789325678 * 342973489379256) :
    (Nat.digits 10 P).length = 34 := by 
  subst hP
  native_decide