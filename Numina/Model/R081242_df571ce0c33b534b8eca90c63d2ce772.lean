import Mathlib

theorem algebra_14616 : {x : ℕ | 0 < x ∧ x < 250 ∧ 5 ∣ x ∧ ¬10 ∣ x}.encard = 25 := by
  have h1 : {x : ℕ | 0 < x ∧ x < 250 ∧ 5 ∣ x ∧ ¬10 ∣ x} = Finset.filter (fun x => 0 < x ∧ x < 250 ∧ 5 ∣ x ∧ ¬10 ∣ x) (Finset.Icc 0 250) := by
    ext x
    simp
    omega
  rw [h1]
  rw [Finset.filter]
  simp [Finset.Icc]
  <;> try native_decide
  <;> try simp [Set.encard]
  all_goals try native_decide