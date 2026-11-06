import Mathlib

theorem number_theory_4972
    (a : Finset ℕ)
    (ha : a = {2, 3, 4, 7, 11, 13, 16}) :
    a.powerset.filter (fun x => x.sum id = 18) =
    {
      {2, 3, 13},
      {2, 16},
      {3, 4, 11},
      {7, 11}
    } := by 
  rw [ha]
  native_decide