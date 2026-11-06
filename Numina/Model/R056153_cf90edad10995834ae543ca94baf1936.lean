import Mathlib

theorem number_theory_270022 {n : ℕ} (hn : n = 8987) :
    n.primeFactors.card = 3 ∧
    ∑ p ∈ n.primeFactors, p^2 = 2331 ∧
    {x | x < n ∧ Nat.Coprime x n}.encard = 7560 ∧
    ∑ d ∈ n.divisors, d = 10560 := by
  rw [hn]
  constructor
  · -- Show that 8987 has exactly 3 prime factors.
    native_decide
  constructor
  · -- Show that the sum of the squares of its prime factors is 2331
    native_decide
  constructor
  · -- Show that there are 7560 numbers less than 8987 and coprime with it
    have h1 : {x | x < 8987 ∧ Nat.Coprime x 8987}.encard = 7560 := by
      have hphi : Nat.totient 8987 = 7560 := by
        native_decide
      have h2 : {x | x < 8987 ∧ Nat.Coprime x 8987} = Finset.filter (fun x => Nat.Coprime x 8987) (Finset.Iio (8987 : ℕ)) := by
        ext x
        simp
      rw [h2]
      rw [Finset.filter]
      simp [Finset.Iio]
      <;> try { native_decide }
      <;> try { linarith [hphi] }
    exact h1
  · -- Show that the sum of all divisors of 8987 is 10560
    native_decide