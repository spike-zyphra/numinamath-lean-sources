import Mathlib

theorem number_theory_14660 (s : Finset ℕ) (hs : s = (Finset.Icc 0 2004).image (5 ^ ·))
    (h2004 : (Nat.digits 10 (5 ^ 2004)).length = 1401) :
    (s.filter fun n => (Nat.digits 10 n).getLastI = 1).card = 604 := by 
  rw [hs]
  native_decide