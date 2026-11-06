import Mathlib

theorem number_theory_610090 : 
  -- Define τ(n) as the number of divisors of n
  let τ (n : ℕ) : ℕ := (n.divisors).card;
  -- Count integers from 1 to 50 where τ(τ(n)) is odd
  Finset.card {n ∈ Finset.Icc (1 : ℕ) 50 | τ (τ n) % 2 = 1} = 17 := by
  intro τ
  have h1 : {n ∈ Finset.Icc (1 : ℕ) 50 | (τ (τ n)) % 2 = 1} = 
    (Finset.Icc (1 : ℕ) 50).filter (fun n => (τ (τ n)) % 2 = 1) := by
    ext n
    simp
  rw [h1]
  rw [Finset.card_filter]
  native_decide