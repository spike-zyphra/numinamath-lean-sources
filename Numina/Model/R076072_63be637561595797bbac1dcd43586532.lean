import Mathlib

def f (x : ℕ) := Nat.lcm 12 x

theorem number_theory_389 :
    max (max (max (max (f 2) (f 4)) (f 6)) (f 8)) (max (f 10) (f 12)) = 60 := by 
  unfold f 
  native_decide