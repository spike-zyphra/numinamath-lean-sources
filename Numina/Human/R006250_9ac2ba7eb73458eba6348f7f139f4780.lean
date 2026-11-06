import Mathlib

/- Let $N_0$ be the integer $9$. We are interested in numbers of the form $10 N_0 + A$, where $A$ is a digit from the set $\{1, 3, 5, 7, 9\}$. Show that $10 N_0 + 7$ (which is $97$) is prime, and that $10 N_0 + 1$ (which is $91$), $10 N_0 + 3$ (which is $93$), $10 N_0 + 5$ (which is $95$), and $10 N_0 + 9$ (which is $99$) are not prime. -/
theorem number_theory_635159 (N₀ : ℕ) (hN₀ : N₀ = 9) :
    Nat.Prime (10 * N₀ + 7) ∧ ¬ Nat.Prime (10 * N₀ + 1) ∧ ¬ Nat.Prime (10 * N₀ + 3) ∧ ¬ Nat.Prime (10 * N₀ + 5) ∧ ¬ Nat.Prime (10 * N₀ + 9) := by
  -- We judge the prime numbers by `norm_num`.
  norm_num [hN₀]
