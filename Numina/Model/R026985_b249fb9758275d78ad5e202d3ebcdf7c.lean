import Mathlib

lemma lemma_1 (n : ℕ) (h : 1 < n) : 4 ∣ 2^n := by
  have h1 : n ≥ 2 := by linarith
  have h2 : 2^n % 4 = 0 := by
    have h4 : n ≥ 2 := by omega
    have h6 : ∀ k : ℕ, 2 ^ (2 + k) % 4 = 0 := by
      intro k
      induction k with
      | zero =>
        norm_num
      | succ k ih =>
        simp [Nat.pow_add, Nat.pow_succ, Nat.mul_mod] at ih ⊢
        all_goals omega
    have h7 : ∃ k' : ℕ, n = 2 + k' := by
      refine ⟨n - 2, ?_⟩
      omega
    rcases h7 with ⟨k', hk'⟩
    rw [show n = 2 + k' by linarith [hk']]
    apply h6 k'
  omega

theorem number_theory_184210 (n : ℕ) (hn : 1 < n) : (2^(2^n) + 1) % 10 = 7 := by
  have h1 : n ≥ 2 := by linarith
  have h2 : (2 ^ (2 ^ n)) % 10 = 6 := by
    have h3 : ∀ k : ℕ, (2 ^ (2 ^ (k + 2)) ) % 10 = 6 := by
      intro k
      induction k with
      | zero =>
        norm_num
      | succ k ih =>
        have h5 : 2 ^ (2 ^ ((k + 1 + 2 : ℕ)) ) = (2 ^ (2 ^ ((k + 2 : ℕ))) ) ^ 2 := by
          ring_nf
        rw [h5]
        have h8 : ((2 ^ (2 ^ ((k + 2 : ℕ))) ) ^ 2) % 10 = 6 := by
          have h9 : (2 ^ (2 ^ ((k + 2 : ℕ))) ) % 10 = 6 := ih
          norm_num [Nat.pow_mod, h9]
        exact h8
    have h7 : n ≥ 2 := by linarith
    have h8 : ∃ k : ℕ, n = k + 2 := by
      refine ⟨n - 2, ?_⟩
      omega
    rcases h8 with ⟨k, hk⟩
    rw [show n = k + 2 by linarith [hk]]
    apply h3 k
  omega