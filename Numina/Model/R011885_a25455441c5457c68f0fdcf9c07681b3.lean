import Mathlib

open Finset

theorem number_theory_162979 (S : Finset ℕ) (hS : S = {0, 2, 4, 5, 7, 9}) :
    #((S ×ˢ S ×ˢ S ×ˢ S ×ˢ S).filter (fun (a, b, c, d, e) => 15 ∣ Nat.ofDigits 10 [e, 2, 0, d, c, b, a, 6, 1, 0, 2])) = 864 := by
  simp [hS]
  <;> native_decide