import Mathlib

theorem number_theory_264877 : {n : ℕ | n < 56700000 ∧ Nat.Coprime n 56700000}.encard = 12960000 := by
  have h1 : {n : ℕ | n < 56700000 ∧ Nat.Coprime n 56700000} = Finset.filter (λ n => Nat.Coprime n 56700000) (Finset.Iio 56700000) := by
    ext n
    simp
  rw [h1]
  rw [Finset.filter]
  simp [Finset.Iio]
  native_decide