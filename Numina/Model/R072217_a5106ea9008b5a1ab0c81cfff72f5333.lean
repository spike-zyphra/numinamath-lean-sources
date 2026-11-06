import Mathlib

theorem number_theory_203470 {n : ℕ} (hn : n = 3659893456789325678 * 342973489379256) :
    (Nat.digits 10 n).length = 34 := by 
  subst hn
  native_decide