import Mathlib

/-The number of apples that Sophia has is a multiple of $6$. When she sells one apple, the number of apples is a multiple of $n$. If $n$ is a positive integer less than $10$, how many possible values are there for $n$?-/
theorem number_theory_23417 :
    Set.ncard {n : ℕ | 0 < n ∧ n < 10 ∧ ∃ k > 0, 6 ∣ k ∧ (k - 1) % n = 0 } = 3 := by
  -- Let $a$ be the number of apples that Sophia originally had. Clearly $a=6b$ for some positive integer $b$. Additionally, $a-1\equiv 0\pmod n\implies 6b\equiv 1\pmod n$. This is solvable for $b$ if and only if $6$ is invertible modulo $n$. In other words, $\gcd(6,n)=1$. The only such $n$ less than $10$ are $1,5,7$, so there are $\boxed{3}$ possibilities for $n$.
  have : {n : ℕ | 0 < n ∧ n < 10 ∧ ∃ k > 0, 6 ∣ k ∧ (k - 1) % n = 0 } =
         {1, 5, 7} := by
    ext n
    simp
    constructor
    · -- {n : ℕ | 0 < n ∧ n < 10 ∧ ∃ k > 0, 6 ∣ k ∧ (k - 1) % n = 0 }
      -- is the subset of {1, 5, 7}
      rintro ⟨hn₁, hn₂, k, hk₀, hk₁, hk₂⟩
      have hn₃: 1 ≤ n := by linarith
      rcases hk₁ with ⟨b, hb⟩
      have : 6 * b ≡ 1 [MOD n] := by
        rw [hb.symm, Nat.ModEq]
        obtain ⟨p, hp⟩ := show ∃p, k = p + 1 by
          use (k - 1)
          omega
        rw [hp]
        rw [hp] at hk₂
        simp at hk₂
        rw [Nat.add_mod, hk₂]
        simp
      interval_cases n <;> omega
    · -- {1, 5, 7} is a subset of {n : ℕ | 0 < n ∧ n < 10 ∧ ∃ k > 0, 6 ∣ k ∧ (k - 1) % n = 0 }
      rintro (hn | hn | hn)
      all_goals
        rw [hn]
        simp
        use 36
        omega
  rw [this]
  simp
