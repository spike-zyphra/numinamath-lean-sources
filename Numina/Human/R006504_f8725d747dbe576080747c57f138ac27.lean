import Mathlib

/-Let $k$ be a positive integer, and let $N_k = 100k$.
Determine the last two digits of the central binomial coefficient $\binom{2N_k}{N_k}$.
Show that for $k=1$ (i.e., $N_1=100$), the last two digits are 40, and for $k=2$ (i.e., $N_2=200$), the last two digits are 20.-/

theorem number_theory_637826 (k N_k: ℕ) (hN: N_k = 100 * k):
  (k = 1 → (Nat.choose (2 * (N_k)) (N_k)) % 100 = 20) ∧ (k = 2 → (Nat.choose (2 * (N_k)) (N_k)) % 100 = 20) := by

  constructor
  .
    intro h
    simp [h] at hN
    simp [hN]
    native_decide
  .
    intro h
    simp [h] at hN
    simp [hN]
    native_decide
