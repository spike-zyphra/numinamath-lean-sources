import Mathlib

theorem number_theory_206083 {A : ℕ} (hA : A = ∑ i ∈ Finset.range 221, 10 ^ i * 9) :
    (Nat.digits 10 (A ^ 2)).sum = 1989 := by
  rw [hA]
  native_decide