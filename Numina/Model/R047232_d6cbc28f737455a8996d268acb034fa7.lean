import Mathlib

theorem algebra_20651 (s t : Finset ℕ) (hs : s = (Finset.Ioo 40 60).filter Nat.Prime)
    (ht : t = s.filter fun p => (p + 12).Prime) :
    t.card / s.card = (3 / 5 : ℚ) := by
  have h1 : s = {41, 43, 47, 53, 59} := by 
    rw [hs]
    native_decide
  have h2 : t = {41, 47, 59} := by 
    rw [ht, h1]
    native_decide
  rw [h2, h1]
  native_decide