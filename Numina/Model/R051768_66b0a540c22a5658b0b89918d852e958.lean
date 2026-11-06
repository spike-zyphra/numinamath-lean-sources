import Mathlib

theorem algebra_264394 (a : ℕ) (ha : a = Nat.factorial 1580) :
    ∑ i in Finset.Icc 1 1580, i * Nat.factorial i = 1581 * a - 1 := by
  rw [ha]
  native_decide