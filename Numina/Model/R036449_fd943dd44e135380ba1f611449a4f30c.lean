import Mathlib

open Finset

theorem number_theory_166580 {φ : ℕ → ℕ}
    (hφ : ∀ n, φ n = ∏ m ∈ (Icc 1 n).filter (fun x => Nat.Coprime x n), m) :
    {n | 2 ≤ n ∧ n ≤ 50 ∧ n ∣ φ n + 1}.ncard = 30 := by
  have h1 : {n | 2 ≤ n ∧ n ≤ 50 ∧ n ∣ φ n + 1} = Finset.filter (fun n => 2 ≤ n ∧ n ≤ 50 ∧ n ∣ φ n + 1) (Finset.Icc 0 50) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  simp [hφ]
  <;> native_decide