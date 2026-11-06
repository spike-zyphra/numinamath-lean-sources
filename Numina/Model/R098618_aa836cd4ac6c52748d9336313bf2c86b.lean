import Mathlib

theorem number_theory_6651 : {x : ℕ | Odd x ∧ 1 ≤ x ∧ x < 1000 ∧ 3 ∣ x ∧ ¬5 ∣ x}.encard = 134 := by 
  have h1 : {x : ℕ | Odd x ∧ 1 ≤ x ∧ x < 1000 ∧ 3 ∣ x ∧ ¬5 ∣ x} = Finset.filter (fun x => Odd x ∧ 3 ∣ x ∧ ¬5 ∣ x) (Finset.Icc (1:ℕ) 999) := by
    ext x
    simp [Nat.odd_iff]
    <;> omega 
  rw [h1]
  rw [Finset.filter]
  simp [Finset.Icc]
  <;> try native_decide
  <;> try simp [Set.encard]
  <;> try native_decide