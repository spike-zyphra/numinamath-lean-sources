import Mathlib

theorem number_theory_195494 (p : ℕ) (hp : Nat.Prime p) (h : 3 ≤ p) :
    ∀ n, ∃ x : ℕ, x > n ∧ ∃ i ∈ Finset.Icc (x + 1) (x + (p + 3) / 2), ∃ q : ℕ, Nat.Prime q ∧ q > p ∧ q ∣ i := by
  intro n
  have h44 : ∃ q : ℕ, q > max p (n + (p + 3) / 2) ∧ Nat.Prime q := by
    have h99 : ∀ (N : ℕ), ∃ q : ℕ, q > N ∧ Nat.Prime q := by
      intro N 
      apply Nat.exists_infinite_primes
    specialize h99 (max p (n + (p + 3) / 2))
    rcases h99 with ⟨q, h10, h11⟩
    exact ⟨q, h10, h11⟩
  rcases h44 with ⟨q, hq3, hq4⟩
  use q - (p + 3) / 2
  constructor
  · -- Show x > n.
    have h88 : q > n + (p + 3) / 2 := by
      have h41 : q > max p (n + (p + 3) / 2) := by linarith
      have h42 : max p (n + (p + 3) / 2) ≥ n + (p + 3) / 2 := by 
        cases max_cases p (n + (p + 3) / 2) with
        | inl h => 
          omega
        | inr h => 
          omega
      omega
    have h22 : q ≥ (p + 3) / 2 := by
      have h10 : q > p := by
        have h11 : q > max p (n + (p + 3) / 2) := by linarith
        have : max p (n + (p + 3) / 2) ≥ p := by
          cases max_cases p (n + (p + 3) / 2) with
          | inl h =>
            omega
          | inr h =>
            omega
        omega
      have h11 : q > (p + 3) / 2 := by
        have h12 : p ≥ (p + 3) / 2 := by
          omega
        omega
      omega
    omega
  · -- Show the existence of i and q.
    use q 
    constructor
    · -- Show that i ∈ Finset.Icc (x + 1) (x + (p + 3) / 2)
      have h55 : q ≥ (p + 3) / 2 := by
        have h10 : q > p := by
          have h11 : q > max p (n + (p + 3) / 2) := by linarith
          have : max p (n + (p + 3) / 2) ≥ p := by
            cases max_cases p (n + (p + 3) / 2) with
            | inl h =>
              omega
            | inr h =>
              omega
          omega
        have h11 : q > (p + 3) / 2 := by
          have h12 : p ≥ (p + 3) / 2 := by
            omega
          omega
        omega
      have h66 : q ∈ Finset.Icc (q - (p + 3) / 2 + 1) (q - (p + 3) / 2 + (p + 3) / 2) := by
        simp at *
        all_goals
          omega
      exact h66
    · -- Show the existence of q.
      use q 
      constructor
      · -- Show Nat.Prime q 
        exact hq4
      constructor
      · -- Show q > p 
        have h10 : q > p := by
          have h11 : q > max p (n + (p + 3) / 2) := by linarith
          have : max p (n + (p + 3) / 2) ≥ p := by
            cases max_cases p (n + (p + 3) / 2) with
            | inl h =>
              omega
            | inr h =>
              omega
          omega
        omega
      · -- Show q ∣ i 
        have h77 : q ∣ q := by 
          exact dvd_refl q
        exact h77