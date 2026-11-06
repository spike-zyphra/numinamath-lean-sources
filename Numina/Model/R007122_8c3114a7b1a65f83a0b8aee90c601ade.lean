import Mathlib

theorem number_theory_56387 : {n : ℕ | 0 < n ∧ n ≤ 2009 ∧ (n ^ 20) % 10 = 1}.encard = 804 := by
  have h1 : {n : ℕ | 0 < n ∧ n ≤ 2009 ∧ (n ^ 20) % 10 = 1} = Finset.filter (fun n => 0 < n ∧ n ≤ 2009 ∧ (n ^ 20) % 10 = 1) (Finset.Icc 0 2009) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide