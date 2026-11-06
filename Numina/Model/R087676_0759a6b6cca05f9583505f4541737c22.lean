import Mathlib

theorem number_theory_107150 : {n : ℕ | 1 ≤ n ∧ n ≤ 221 ∧ (221 % n) % (221 / n) = 0}.encard = 115 := by
  have h1 : {n : ℕ | 1 ≤ n ∧ n ≤ 221 ∧ (221 % n) % (221 / n) = 0} = Finset.filter (fun n => 1 ≤ n ∧ n ≤ 221 ∧ (221 % n) % (221 / n) = 0) (Finset.Icc 0 221) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide