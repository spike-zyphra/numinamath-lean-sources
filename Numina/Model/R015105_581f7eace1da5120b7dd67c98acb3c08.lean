import Mathlib

theorem algebra_14962 : {n : ℕ | Even n ∧ n > 202 ∧ n < 405}.encard = 101 := by
  have h2 : {n : ℕ | Even n ∧ n > 202 ∧ n < 405} = Finset.filter (fun (n : ℕ) => Even n) (Finset.Icc 203 404) := by
    ext n
    simp [Finset.mem_Icc, Nat.even_iff]
    <;> omega
  rw [h2]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide