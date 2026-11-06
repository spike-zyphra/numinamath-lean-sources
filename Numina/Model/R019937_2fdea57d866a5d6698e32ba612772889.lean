import Mathlib

theorem number_theory_162854 :
    {x : ℕ | x > 0 ∧ x ∣ Nat.factorial 12 ∧ x % 3 = 1}.encard = 66 := by
  have h1 : {x : ℕ | x > 0 ∧ x ∣ Nat.factorial 12 ∧ x % 3 = 1} = Finset.filter (fun x => x > 0 ∧ x % 3 = 1) (Nat.factorial 12).divisors := by
    ext n
    simp
    <;> tauto
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide