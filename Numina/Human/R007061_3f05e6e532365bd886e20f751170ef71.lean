import Mathlib

theorem number_theory_181835 {a b : ℕ} (ha : a = ∑ i ∈ Finset.range 2016, 10 ^ i)
    (hb : b = ∑ i ∈ Finset.range 1008, 2 * 10 ^ i) :
    IsSquare (a - b : ℤ) := by 
  rw [ha, hb]
  native_decide