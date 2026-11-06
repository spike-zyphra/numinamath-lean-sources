import Mathlib

theorem algebra_192491 {x : ℕ} (hx : x < 100) (hx1 : x > 9)
    (hxp : (Nat.digits 10 x).prod = 24) (hxr : Nat.ofDigits 10 (List.reverse (Nat.digits 10 x)) = x + 18) :
    x = 46 := by 
  interval_cases x <;> simp [Nat.ofDigits, Nat.digits, Nat.digitsAux] at hxp hxr ⊢ <;> all_goals norm_num at hxp hxr <;> all_goals trivial