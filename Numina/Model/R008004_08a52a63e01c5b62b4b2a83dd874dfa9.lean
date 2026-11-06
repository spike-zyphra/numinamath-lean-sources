import Mathlib

open Nat Finset List

theorem number_theory_97342 {N : ℕ}
    (hN : N = (ofDigits 10 $ (List.Ico 1 45) |>.reverse |>.map (fun n ↦ digits 10 n) |>.foldr List.append [])) :
    N % 45 = 9 := by
  rw [hN]
  native_decide