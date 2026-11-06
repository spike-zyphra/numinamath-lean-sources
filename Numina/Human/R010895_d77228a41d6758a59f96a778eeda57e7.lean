import Mathlib

theorem number_theory_608730 : ∑ᶠ i ∈ {n : ℕ | n ≤ 511 ∧ Even ((Nat.digits 2 n).count 1)}, i = 65408 := by
  have h₁ : {n : ℕ | n ≤ 511 ∧ Even ((Nat.digits 2 n).count 1)} = Finset.filter (λn ↦ (Nat.digits 2 n).count 1 % 2 = 0) (Finset.Icc 0 511) := by
    ext n; simp
    rw [Nat.even_iff]
    tauto
  have h₂ : ∑ᶠ (i : ℕ) (_ : i ∈ ↑(Finset.filter (fun n ↦ List.count 1 (Nat.digits 2 n) % 2 = 0) (Finset.Icc 0 511) : Set ℕ)), i = ∑ i ∈ Finset.filter (λn ↦ (Nat.digits 2 n).count 1 % 2 = 0) (Finset.Icc 0 511), i := by
    apply finsum_mem_finset_eq_sum
  rw [h₁, h₂]
  native_decide
