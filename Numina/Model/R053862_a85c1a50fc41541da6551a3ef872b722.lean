import Mathlib

open Finset

theorem number_theory_314773 {f : ℕ → ℕ → ℕ}
    (hf : ∀ n k, f n k = {x | x > 0 ∧ x ≤ n / k ∧ Nat.Coprime x n}.ncard) :
    f 100 3 = 14 := by
  have h : f 100 3 = {x | x > 0 ∧ x ≤ (100 : ℕ) / 3 ∧ Nat.Coprime x 100}.ncard := hf 100 3
  rw [h]
  have : {x | x > 0 ∧ x ≤ (100 : ℕ) / 3 ∧ Nat.Coprime x 100} =Finset.filter (fun x => x > 0 ∧ x ≤ (100 : ℕ) / 3 ∧ Nat.Coprime x 100) (Finset.Icc 0 (34)) := by 
    ext x 
    simp 
    omega 
  rw [this]
  rw [Finset.filter]
  simp [Finset.Icc]
  <;> try native_decide