import Mathlib

/-Let $M$ be a positive integer. A positive integer $N$ is divisible by $M$. All its digits (in base 10) are different.
If any two of its digits are swapped, the resulting number $N'$ (obtained by swapping the two digits) is not divisible by $M$.
If $M=10$, show that $N$ must have 2 digits.-/

theorem number_theory_639575 (N: ℤ) (n: ℕ) (a: ℕ → ℤ) (h0: ∀ i, 0 ≤ a i ∧ a i ≤ 9) (h1: a n ≠ 0)
(h2: N = ∑ i ∈ Finset.Icc 0 n, 10 ^ i * a i) (h3: 10 ∣ N)
(h4: ∀ i j, i < j ∧ j ≤ n → ¬ 10 ∣ N + 10 ^ j * a i + 10 ^ i * a j - 10 ^ i * a i - 10 ^ j * a j):
  n = 1 := by

  by_contra! l
  replace l: n = 0 ∨ 2 ≤ n := by
    omega
  rcases l with l | l

  -- case1: n = 0
  .
    simp [l] at h2 h1
    specialize h0 0
    clear *- h2 h1 h0 h3
    omega

  -- case2: n ≥ 2
  .
    specialize h4 1 2 (by omega)
    absurd h4
    rw [show N + 10 ^ 2 * a 1 + 10 ^ 1 * a 2 - 10 ^ 1 * a 1 - 10 ^ 2 * a 2 =
      N + (10 ^ 2 * a 1 + 10 ^ 1 * a 2 - 10 ^ 1 * a 1 - 10 ^ 2 * a 2) by abel]
    apply Int.dvd_add
    .
      tauto
    .
      omega