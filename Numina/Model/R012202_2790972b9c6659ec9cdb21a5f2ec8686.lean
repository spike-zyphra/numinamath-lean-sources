import Mathlib
open Mathlib
theorem number_theory_1200 (s : Finset ℕ) (h : ∀ x, x ∈ s ↔ 0 < x ∧ x < 1000 ∧ x = 6 * (Nat.digits 10 x).sum) : s.card = 1 := by
  have h1 : s = Finset.filter (fun x => 0 < x ∧ x < 1000 ∧ x = 6 * (Nat.digits 10 x).sum) (Finset.Icc 0 999) := by
    ext x
    simp [h]
    <;> omega
  rw [h1]
  native_decide