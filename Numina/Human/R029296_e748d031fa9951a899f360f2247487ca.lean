import Mathlib

/- Prover qu'il n'existe qu'un nombre fini de nombres premiers s'écrivant sous la forme $n^{3}+2 n+3$ avec $n \in \mathbb{N}$. -/
/- Prouver qu'il n'existe qu'un nombre fini de nombres premiers s'écrivant sous la forme $n^{3}+2 n+3$ avec $n \in \mathbb{N}$. -/
theorem number_theory_607604 :
    Set.Finite {p | p.Prime ∧ ∃ n, p = n^3 + 2 * n + 3} := by
  -- Prove that for all natural numbers $n$, $n^3 + 2n + 3$ is always divisible by $3$.
  have h₁ : ∀ n : ℕ, (n^3 + 2 * n + 3) % 3 = 0 := by
    intro n
    have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases this with (h | h | h) <;> simp [h, pow_succ, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
  -- Determine that when $n^3 + 2n + 3 = 3$, the only natural number solution is $n = 0$.
  have h₂ : ∀ n : ℕ, n^3 + 2 * n + 3 = 3 → n = 0 := by
    intro n hn
    contrapose! hn
    have : n ≥ 1 := by omega
    have : n^3 + 2 * n + 3 ≥ 1^3 + 2 * 1 + 3 := by gcongr
    omega
  -- Prove that for all $n ≥ 1$, $n^3 + 2n + 3$ is a multiple of $3$ and greater than $3$, hence composite.
  have h₃ : ∀ n : ℕ, n ≥ 1 → ¬ Nat.Prime (n^3 + 2 * n + 3) := by
    intro n hn
    have h_div_3 : 3 ∣ n^3 + 2 * n + 3 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      exact h₁ n
    have h_gt_3 : n^3 + 2 * n + 3 > 3 := by
      have : n^3 + 2 * n + 3 ≥ 1^3 + 2 * 1 + 3 := by gcongr
      norm_num at this 
      linarith
    have h_not_prime : ¬ Nat.Prime (n^3 + 2 * n + 3) := by
      apply Nat.not_prime_of_dvd_of_lt h_div_3
      · norm_num
      · exact h_gt_3
    exact h_not_prime
  -- The only prime of the form $n^3 + 2n + 3$ is $3$, generated when $n = 0$, so the set is finite.
  refine' Set.Finite.subset (Set.finite_singleton 3) _
  rintro p ⟨hp, n, rfl⟩
  have : n = 0 := by
    by_contra!
    exact h₃ n (by omega) hp
  simp [this]