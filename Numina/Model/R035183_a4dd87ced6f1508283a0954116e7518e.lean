import Mathlib

theorem number_theory_8166 (n : ℕ) (hn : n > 0) :
    ∃ k, ∀ i ∈ Finset.range n, ¬Nat.Prime (k + i) := by

  use (n + 1).factorial + 2

  intro i hi

  have h1 : i < n := by 
    simpa using hi

  -- $k$ is $(n + 1)! + 2$. For any $i \in \range(n)$, we need to prove that
  -- $k + i$ is not prime. Let's see $k + i = (n + 1)! + 2 + i = (n + 1)! + (i + 2)$.
  -- Since $i < n$, we have $i \leq n - 1$, so $i + 2 \leq n + 1$.
  have h2 : i + 2 ≤ n + 1 := by
    omega

  -- Then $i + 2$ divides $(n + 1)!$.
  have h3 : (i + 2) ∣ (n + 1).factorial := by 
    apply Nat.dvd_factorial
    all_goals 
      omega

  -- So $i + 2$ divides $(n + 1)! + (i + 2)$.
  have h4 : (i + 2) ∣ ((n + 1).factorial + (i + 2)) := by 
    apply Nat.dvd_add
    exact h3
    simp

  -- Let's see $k + i = (n + 1)! + 2 + i = (n + 1)! + (i + 2)$, so $k + i$ is equal to $(n +1)! + (i + 2)$
  -- which is divisible by $i + 2$, which is $\geq 2$.
  -- Thus $k + i$ is not prime.
  have h5 : ¬Nat.Prime ((n + 1).factorial + (i + 2)) := by 
    apply Nat.not_prime_of_dvd_of_lt h4 
    all_goals 
      nlinarith [Nat.factorial_pos (n + 1)]

  -- We need to show $\neg$Nat.Prime $k + i$
  have h6 : (n + 1).factorial + 2 + i = (n + 1).factorial + (i + 2) := by 
    omega

  rw [h6]
  exact h5