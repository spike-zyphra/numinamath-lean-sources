import Mathlib

theorem algebra_12584 : {x : ℕ | 62 ≤ x ∧ x < 215 ∧ 3 ∣ x}.encard = 51 := by
  have h1 : {x : ℕ | 62 ≤ x ∧ x < 215 ∧ 3 ∣ x} = Finset.filter (fun x => 3 ∣ x) (Finset.Icc (62 : ℕ) 214) := by
    ext x
    simp
    omega
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide