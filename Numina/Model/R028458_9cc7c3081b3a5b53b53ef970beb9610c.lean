import Mathlib

theorem number_theory_161022 (n : ℕ) (hn : 1 ≤ n) :
    ∃ k, ∀ i ∈ Finset.Icc k (k + n - 1), ¬Nat.Prime i := by 
  use (n + 1).factorial + 2
  intro i hi
  rw [Finset.mem_Icc] at hi
  rcases hi with ⟨h1, h2⟩
  -- Assume i is in the interval
  -- so need to show ¬Nat.Prime i
  -- We have i in the range from (n + 1)! + 2 to (n + 1)! + n + 1
  have h5 : i - ((n + 1).factorial : ℕ) ≥ 2 := by
    omega
  have h6 : i - ((n + 1).factorial : ℕ) ≤ n + 1 := by
    omega
  have h7 : ∃ j, i = (n + 1).factorial + j ∧ 2 ≤ j ∧ j ≤ n + 1 := by 
    use i - ((n + 1).factorial : ℕ)
    constructor 
    · -- Show i = (n + 1)! + j
      omega 
    constructor 
    · -- Show 2 ≤ j
      omega 
    · -- Show j ≤ n + 1
      omega 
  rcases h7 with ⟨j, h8, h9, h10⟩
  -- j divides (n+1)!
  have h11 : j ∣ (n + 1).factorial := by
    apply Nat.dvd_factorial
    all_goals 
      omega
  -- j divides i = (n+1)! +j
  have h12 : j ∣ i := by
    rw [h8]
    apply Nat.dvd_add 
    exact h11 
    simp 
  -- i >j
  have h13 : i > j := by
    nlinarith [Nat.factorial_pos (n + 1), h9]
  -- j >1
  have h14 : j > 1 := by 
    omega 
  -- i not prime
  have h14 : ¬Nat.Prime i := by 
    apply Nat.not_prime_of_dvd_of_lt h12 
    all_goals 
      omega 
  exact h14