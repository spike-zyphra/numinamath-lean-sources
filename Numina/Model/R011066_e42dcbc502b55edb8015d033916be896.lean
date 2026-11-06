import Mathlib

open Finset

theorem number_theory_610514 :
    {(a, b) | 1 ≤ a ∧ a < b ∧ b ≤ 57 ∧ a ^ 2 % 57 < b ^ 2 % 57}.ncard = 738 := by
  have h : {(a, b) | 1 ≤ a ∧ a < b ∧ b ≤ 57 ∧ a ^ 2 % 57 < b ^ 2 % 57} = Finset.filter (fun p : ℕ × ℕ => 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 57 ∧ p.1 ^ 2 % 57 < p.2 ^ 2 % 57) (Finset.Icc (0 : ℕ) 57 ×ˢ Finset.Icc (0 : ℕ) 57) := by
    ext ⟨a, b⟩
    simp
    omega
  rw [h]
  rw [Set.ncard_coe_Finset]
  native_decide