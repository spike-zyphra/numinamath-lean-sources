import Mathlib

theorem number_theory_58916 {A : ℕ} (hA : A = ∑ i ∈ Finset.range 165, 2013 * 10 ^ (i * 4)) :
    2013 ^ 2 ∣ A := by 
  rw [hA]
  native_decide