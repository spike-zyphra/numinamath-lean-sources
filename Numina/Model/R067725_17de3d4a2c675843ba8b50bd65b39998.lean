import Mathlib

theorem number_theory_314272 : {n | 0 ≤ n ∧ n ≤ 2015 ∧ 7 ∣ Nat.choose 2015 n}.encard = 1722 := by 
  have h1 : {n | 0 ≤ n ∧ n ≤ 2015 ∧ 7 ∣ Nat.choose 2015 n} = Finset.filter (λ n => 7 ∣ Nat.choose 2015 n) (Finset.Icc 0 2015) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide