import Mathlib

theorem number_theory_12993 : {x : ℕ | 0 < x ∧ x ≤ 2018 ∧ Nat.gcd x 2018 = 1}.encard = 1008 := by
  have h1 : {x : ℕ | 0 < x ∧ x ≤ 2018 ∧ Nat.gcd x 2018 = 1} = Finset.filter (λ x => 0 < x ∧ x ≤ 2018 ∧ Nat.gcd x 2018 = 1) (Finset.Icc 0 2018) := by
    ext n
    simp
    <;> omega
  rw [h1] at *
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide