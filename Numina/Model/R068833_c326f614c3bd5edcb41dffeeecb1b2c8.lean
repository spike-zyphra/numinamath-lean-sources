import Mathlib

open Finset

theorem number_theory_142212 {f : ℕ → ℕ → ℕ}
    (hf : ∀ n k, f n k = {x | 0 < x ∧ x ≤ n / k ∧ Nat.Coprime x n}.ncard) :
    f 100 3 = 14 := by 
  rw [hf 100 3]
  have : {x | 0 < x ∧ x ≤ 33 ∧ Nat.Coprime x 100} = 
      (Finset.Icc 0 33).filter (λ x => 0 < x ∧ x ≤ 33 ∧ Nat.Coprime x 100) := by
    ext x
    simp 
    <;> tauto 
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide