import Mathlib

theorem number_theory_608730 : ∑ᶠ i ∈ {n : ℕ | n ≤ 511 ∧ Even ((Nat.digits 2 n).count 1)}, i = 65408 := by
have h₁ : {n : ℕ | n ≤ 511 ∧ Even ((Nat.digits 2 n).count 1)} = Finset.filter (λn ↦ (Nat.digits 2 n).count 1 % 2 = 0) (Finset.Icc 0 511) := by
  ext n 
  simp [Nat.even_iff]
rw [h₁]
rw [finsum_mem_coe_finset]
simp [Finset.filter]
<;> try { native_decide }