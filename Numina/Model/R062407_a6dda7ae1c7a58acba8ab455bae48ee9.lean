import Mathlib

theorem number_theory_6872 : {x : ℕ | x < 1331 ∧ Nat.Coprime x 1331}.encard = 1210 := by
  have h1 : {x : ℕ | x < 1331 ∧ Nat.Coprime x 1331} = Finset.filter (λ x => Nat.Coprime x 1331) (Finset.Iio 1331) := by
    ext n
    simp
  rw [h1]
  rw [Finset.filter]
  simp [Finset.Iio]
  <;> try native_decide