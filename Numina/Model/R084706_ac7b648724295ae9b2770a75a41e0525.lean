import Mathlib

theorem number_theory_6776 : {n : ℕ | n < 840 ∧ Nat.Coprime n 840}.encard = 192 := by
  have h1 : {n : ℕ | n < 840 ∧ Nat.Coprime n 840} = Finset.filter (λ n => Nat.Coprime n 840) (Finset.Iio (840 : ℕ)) := by
    ext n
    simp
    <;> try { tauto }
  rw [h1]
  rw [Finset.filter]
  simp [Finset.Iio]
  <;> try { native_decide }