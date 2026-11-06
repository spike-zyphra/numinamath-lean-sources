import Mathlib

theorem number_theory_176833 : {n : ℕ | n < 50 ∧ Odd (Nat.divisors n).card}.encard = 7 := by
  have : {n : ℕ | n < 50 ∧ Odd (Nat.divisors n).card} = 
    (Finset.Iio 50).filter (fun n => Odd (Nat.divisors n).card) := by
    ext n
    simp
  rw [this]
  rw [Finset.filter]
  simp [Finset.Iio]
  aesop