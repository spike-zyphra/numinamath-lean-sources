import Mathlib

open Finset

theorem number_theory_210243 {f : ℕ → ℕ → ℕ}
    (hf : ∀ n k, f n k = {x | x > 0 ∧ x ≤ n / k ∧ Nat.Coprime x n}.ncard) :
    f 100 3 = 14 := by
  have h1 : f 100 3 = {x | x > 0 ∧ x ≤ 100 / 3 ∧ Nat.Coprime x 100}.ncard := by
    specialize hf 100 3
    simpa using hf
  rw [h1]
  have h2 : 100 / 3 = 33 := by 
    norm_num
  rw [h2]
  have : {x | x > 0 ∧ x ≤ 33 ∧ Nat.Coprime x 100} = 
          Finset.filter (fun x => x > 0 ∧ x ≤ 33 ∧ Nat.Coprime x 100) (Finset.Icc 0 33) := by
    ext n 
    simp 
    <;> try { 
      omega 
    }
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide