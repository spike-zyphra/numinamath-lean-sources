import Mathlib

theorem number_theory_177917 {a b : ℕ} (ha : a = ∑ i ∈ Finset.range 1985, 10^i * 8) (hb : b = ∑ i ∈ Finset.range 1985, 10^i * 5) :
    (Nat.digits 10 (9 * a * b)).sum = 17865 := by 
  rw [ha, hb]
  native_decide