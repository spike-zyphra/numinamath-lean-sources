import Mathlib

theorem number_theory_146161 (n : ℕ) (hn : 2 ≤ n) :
    ∃ k, ∀ i ∈ Finset.range n, ¬Nat.Prime (k + i) := by
  use (n + 1).factorial + 2
  intro i hi
  have h1 : i < n := by 
    simp [Finset.mem_range] at hi 
    omega 
  -- Note that i + 2 ≤ n + 1
  have h2 : i + 2 ≤ n + 1 := by
    omega 
  -- i + 2 divides (n + 1)! 
  have h3 : i + 2 ∣ (n + 1).factorial := by 
    apply Nat.dvd_factorial 
    all_goals linarith 
  -- i + 2 divides (n + 1)! + 2 + i 
  -- (n + 1)! + 2 + i = (n + 1)! + (i + 2)
  have h4 : i + 2 ∣ ((n + 1).factorial + 2 + i) := by 
    have h5 : i + 2 ∣ (n + 1).factorial := h3 
    have h6 : i + 2 ∣ (2 + i) := by 
      use 1 
      all_goals ring 
    have h7 : i + 2 ∣ ((n + 1).factorial + (2 + i)) := by 
      apply Nat.dvd_add 
      exact h5 
      exact h6 
    have h8 : (n + 1).factorial + 2 + i = (n + 1).factorial + (2 + i) := by ring 
    rw [h8] 
    exact h7 
  -- Therefore, $k + i$ is not prime, since it is divisible by i + 2 > 1
  -- We prove it's not prime
  have h5 : ¬Nat.Prime ((n + 1).factorial + 2 + i) := by 
    apply Nat.not_prime_of_dvd_of_lt h4 
    all_goals 
      nlinarith [Nat.factorial_pos (n + 1), Nat.factorial_pos (n + 1)]
  simpa using h5