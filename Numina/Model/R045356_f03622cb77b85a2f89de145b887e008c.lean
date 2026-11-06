import Mathlib

theorem number_theory_283659 :
    ∑ᶠ p ∈ {p : ℕ | p.Prime ∧ ∃ n, n^2 = p + 1}, p = 3 := by
  have h1 : {p : ℕ | p.Prime ∧ ∃ n, n^2 = p + 1} = {3} := by 
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Assume $p \in \{p : \mathbb{N} | p \text{ is prime } \wedge \exists n, n^2 = p + 1 \}$. Show $p = 3$.
      intro hp
      rcases hp with ⟨h_prime, ⟨n, hn⟩⟩
      have h2 : n ≤ p + 1 := by
        nlinarith
      have h3 : p = n^2 - 1 := by
        omega
      by_cases h4 : n > 2
      · -- Assume $n > 2$.
        -- Now we need to show that $p$ is composite, contradicting $h_prime$.
        -- Note $p = n^2 - 1 = (n - 1)(n + 1)$.
        -- We have $n - 1 > 1$ and $n + 1 > 2$, hence $p$ is composite.
        have h5 : n - 1 > 1 := by 
          omega
        have h6 : n + 1 > 2 := by 
          omega
        -- Show $p = (n-1)(n+1)$.
        have h7 : p = (n - 1) * (n + 1) := by 
          have eq1 : n ^ 2 = (n - 1) * (n + 1) + 1 := by
            cases n with
            | zero => 
              omega 
            | succ n => 
              cases n with
              | zero => 
                omega 
              | succ n => 
                simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
                <;> ring_nf <;> omega 
          have eq2 : n ^ 2 - 1 = (n - 1) * (n + 1) := by 
            omega 
          rw [h3] 
          all_goals 
          omega 
        -- Show $p$ is not prime. 
        have h8 : ¬p.Prime := by 
          rw [h7] 
          apply Nat.not_prime_mul (by omega) (by omega) 
        contradiction
      · -- Assume $n \le 2$.
        -- So $n=0,1,2$.
        have h5 : n ≤ 2 := by 
          omega 
        interval_cases n <;> norm_num [h3] at *
    · -- Assume $p = 3$.
      intro hp 
      rw [hp] 
      constructor 
      · norm_num 
      · use 2 
        all_goals norm_num 
  rw [h1]
  simp