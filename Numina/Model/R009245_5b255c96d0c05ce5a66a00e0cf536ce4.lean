import Mathlib

theorem algebra_12983 :
    Set.ncard {x : ℕ | 1 ≤ x ∧ x ≤ 200 ∧ 3 ∣ x ∧ 5 ∣ x ∧ ¬(4 ∣ x) ∧ ¬(7 ∣ x)} = 9 := by
  have h1 : {x : ℕ | 1 ≤ x ∧ x ≤ 200 ∧ 3 ∣ x ∧ 5 ∣ x ∧ ¬(4 ∣ x) ∧ ¬(7 ∣ x)} = Finset.filter (fun x => 1 ≤ x ∧ x ≤ 200 ∧ 3 ∣ x ∧ 5 ∣ x ∧ ¬(4 ∣ x) ∧ ¬(7 ∣ x)) (Finset.Icc 0 200) := by
    ext x
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide