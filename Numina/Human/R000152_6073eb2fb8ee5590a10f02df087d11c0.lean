import Mathlib

abbrev multmod1 (s : List ℤ) (w : ℤ) (m : ℤ) :=
  s.map (fun x => (w * x) % m)

/-
Find the sequence obtained from the super-increasing sequence $(1,3,5,10,20,41,80)$ when modular multiplication is applied with multiplier $w=17$ and modulus $m=162$.
-/
theorem number_theory_4973 : multmod1 [1, 3, 5, 10, 20, 41, 80] 17 162 =
    [17, 51, 85, 8, 16, 49, 64] := by
  -- verify by computation
  native_decide
