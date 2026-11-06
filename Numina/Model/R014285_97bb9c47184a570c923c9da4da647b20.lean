import Mathlib

theorem number_theory_95411 {a b : ℕ} (ha : a = ∑ i ∈ Finset.range 1985, 8 * 10 ^ i)
    (hb : b = ∑ i ∈ Finset.range 1985, 5 * 10 ^ i) :
    (Nat.digits 10 (9 * a * b)).sum = 17865 := by
  rw [ha, hb]
  native_decide