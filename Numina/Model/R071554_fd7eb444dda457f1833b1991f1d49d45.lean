import Mathlib

theorem algebra_80132 {m n : ℕ} (hm : m > 0) (hn : n > 0)
    (hmn : Nat.Coprime m n) (A : ℚ) (hA : A = (∑ i in Finset.range 1007, (2 * i + 2)) / (∑ i in Finset.range 1007, (2 * i + 1)) -
    (∑ i in Finset.range 1007, (2 * i + 1)) / (∑ i in Finset.range 1007, (2 * i + 2))) :
    A.num = 2015 := by
  rw [hA]
  native_decide