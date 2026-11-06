import Mathlib

def median (X : Multiset ℕ) : ℚ := if Even X.card then ((X.sort (fun a b => a ≤ b))[X.card / 2 - 1]! + (X.sort (fun a b => a ≤ b))[X.card / 2]!) / 2 else (X.sort (fun a b => a ≤ b))[(X.card - 1) / 2]!

theorem algebra_428495 {A B : List ℕ}
    (hA : A = [12, 15, 24, 25, 31, 36, 37, 39, 44, 49, 50])
    (hB : B = [13, 14, 16, 23, 26, 27, 28, 33, 38, 39, 51]) :
    median A + median B = 63 := by
  simp [median, hA, hB]
  native_decide