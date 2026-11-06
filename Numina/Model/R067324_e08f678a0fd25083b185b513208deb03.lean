import Mathlib

theorem number_theory_266934 : {n : ℕ | n ∈ Finset.Icc 1 100 ∧ 6 ∈ Nat.digits 10 n}.encard = 19 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1 100 ∧ 6 ∈ Nat.digits 10 n} = Finset.filter (fun n => 6 ∈ Nat.digits 10 n) (Finset.Icc 1 100) := by
    ext n
    simp
    <;> tauto
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide