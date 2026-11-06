import Mathlib

theorem number_theory_219353 (n : ℕ) (h₀ : 2 ≤ n) : (2^(2^n)) % 10 = 6 := by 
  have h1 : ∀ k : ℕ, (2 ^ (2 ^ (k + 2)) ) % 10 = 6 := by 
    intro k 
    induction k with 
    | zero => 
      norm_num
    | succ k ih => 
      have h2 : (2 ^ (2 ^ (k + 3)) ) % 10 = 6 := by 
        have h3 : (2 ^ (2 ^ (k + 3)) ) % 10 = (2 ^ (2 * (2 ^ (k + 2))) ) % 10 := by 
          have eq1 : (2 ^ (k + 3) ) = (2 * (2 ^ (k + 2)) ) := by 
            ring_nf
          rw [eq1]
        have h4 : (2 ^ (2 * (2 ^ (k + 2))) ) % 10 = ( (2 ^ (2 ^ (k + 2)) ) ^ 2 ) % 10 := by 
          have eq1 : (2 ^ (2 * (2 ^ (k + 2))) ) = ( (2 ^ (2 ^ (k + 2)) ) ) ^ 2 := by 
            rw [← pow_mul]
            <;> ring_nf 
          rw [eq1]
        rw [h3, h4]
        simp [Nat.pow_mod, ih]
      exact h2 
  have h5 : ∃ k, n = k + 2 := by 
    refine ⟨n - 2, by omega⟩
  rcases h5 with ⟨k, hk⟩
  rw [hk]
  exact h1 k