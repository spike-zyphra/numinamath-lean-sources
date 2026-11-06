import Mathlib

theorem number_theory_5868 : {n | n ∈ Finset.Icc 1 666 ∧ 6 ∈ Nat.digits 10 n}.encard = 181 := by
  have h1 : {n | n ∈ Finset.Icc 1 666 ∧ 6 ∈ Nat.digits 10 n} = Finset.filter (λ (n : ℕ) => 6 ∈ Nat.digits 10 n) (Finset.Icc 1 666) := by
    ext n
    simp
    <;> tauto
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide