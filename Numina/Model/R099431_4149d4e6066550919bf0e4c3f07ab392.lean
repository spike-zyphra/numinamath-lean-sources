import Mathlib

theorem algebra_17245 : {x : ℕ | 10 ∣ x ∧ x ∈ Finset.Icc 9 101}.encard = 10 := by 
  have h1 : {x : ℕ | 10 ∣ x ∧ x ∈ Finset.Icc 9 101} = Finset.filter (λ x => 10 ∣ x) (Finset.Icc 9 101) := by
    ext x
    simp
    <;> aesop
  rw [h1]
  rw [Finset.filter]
  simp [Finset.Icc]
  <;> try native_decide
  <;> try trivial
  <;> try trivial
  <;> try trivial
  <;> try tauto
  <;> try native_decide
  all_goals try trivial
  <;> try native_decide