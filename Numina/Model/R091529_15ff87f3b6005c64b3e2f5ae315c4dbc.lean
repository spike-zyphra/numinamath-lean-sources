import Mathlib

theorem number_theory_323138 : {n : ℕ | 1 ≤ n ∧ n ≤ 2006 ∧ ¬Nat.Coprime (n + 4) 30}.encard = 1471 := by
  have h1 : {n : ℕ | 1 ≤ n ∧ n ≤ 2006 ∧ ¬Nat.Coprime (n + 4) 30} = Finset.filter (fun n => 1 ≤ n ∧ n ≤ 2006 ∧ ¬Nat.Coprime (n + 4) 30) (Finset.Icc 0 2006) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide