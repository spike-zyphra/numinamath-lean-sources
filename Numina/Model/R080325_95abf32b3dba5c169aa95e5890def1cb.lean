import Mathlib

theorem algebra_21629 {n : ℕ} (hn : n = 2400) :
    ∃ p : Fin 8 → ℕ, (∀ i, Nat.Prime (p i)) ∧ n = ∏ i, p i := by 
  rw [hn]
  use λ i => match i with 
    | 0 => 2 
    | 1 => 2
    | 2 => 2
    | 3 => 2
    | 4 => 2
    | 5 => 3
    | 6 => 5
    | 7 => 5
  constructor 
  · -- Show that ∀ i, p i is prime
    intro i
    fin_cases i <;> norm_num 
  · -- Show that 2400 = product of primes 
    native_decide