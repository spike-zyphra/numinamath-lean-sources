import Mathlib

open Nat

theorem number_theory_204752 {f : ℕ → ℕ}
    (hf : ∀ n, f n = (Nat.factorization (n !) 2)) :
    ∑ i in Finset.Icc 1 1023, f i = 518656 := by
  rw [Finset.sum_congr rfl (fun i hi => hf i)]
  native_decide