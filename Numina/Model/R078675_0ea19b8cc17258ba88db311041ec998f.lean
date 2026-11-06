import Mathlib

theorem number_theory_163187 : {x : ℕ | x < 100 ∧ Nat.Coprime x 200}.encard = 40 := by
  have h1 : {x : ℕ | x < 100 ∧ Nat.Coprime x 200} = Finset.filter (λ x => x < 100 ∧ Nat.Coprime x 200) (Finset.Icc 0 99) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide