import Mathlib

theorem algebra_21282 : {x : ℕ | ∃ n, x = 2008 - 5 * n ∧ n ≥ 0 ∧ n ≤ 401}.encard = 402 := by
  have h1 : {x : ℕ | ∃ n, x = 2008 - 5 * n ∧ n ≥ 0 ∧ n ≤ 401} = Finset.image (fun n => 2008 - 5 * n) (Finset.Icc 0 401) := by
    ext x
    simp
    <;> try { aesop }
    <;> try { tauto }
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide