import Mathlib

theorem number_theory_199915 : ∀ N : ℕ, ∃ n : ℕ, n > N ∧ 100 ∣ 2^n + n^2 := by 
  intro N 
  have h1 : ∀ (k : ℕ), 100 ∣ 2 ^ (6 + 100 * k) + (6 + 100 * k) ^ 2 := by
    intro k 
    induction k with
    | zero =>
      norm_num 
    | succ k ih =>
      have h2 : 2 ^ (6 + 100 * (k + 1)) + (6 + 100 * (k + 1)) ^ 2 =
          (2 ^ (6 + 100 * k) * 2 ^ 100) + (6 + 100 * k + 100) ^ 2 := by 
        ring_nf 
      rw [h2]
      have h3 : 4 ∣ ( (2 ^ (6 + 100 * k) * 2 ^ 100) + (6 + 100 * k + 100) ^ 2 ) := by
        have h5 : (2 ^ (6 + 100 * k) * 2 ^ 100) % 4 = 0 := by 
          have h8 : (2 ^ (6 + 100 * k)) % 4 = 0 := by
            have h9 : ∀ (m : ℕ), 2 ^ (2 + 2 * m) % 4 = 0 := by 
              intro m 
              induction m with 
              | zero => 
                norm_num 
              | succ m ih => 
                ring_nf at ih ⊢ 
                all_goals omega 
            have h10 : (6 + 100 * k) = 2 + 2 * ((2 + 50 * k) : ℕ) := by 
              omega 
            rw [h10]
            specialize h9 (2 + 50 * k)
            simpa using h9
          have h9 : (2 ^ 100) % 4 = 0 := by
            norm_num 
          simp [Nat.mul_mod, h8, h9]
        have h8 : ((6 + 100 * k + 100) ^ 2) % 4 = 0 := by
          have h9 : (6 + 100 * k + 100) % 2 = 0 := by 
            omega 
          have h10 : (6 + 100 * k + 100) % 4 = 0 ∨ (6 + 100 * k + 100) % 4 = 2 := by 
            omega 
          rcases h10 with (h | h)
          · simp [Nat.pow_mod, h, Nat.add_mod]
          · simp [Nat.pow_mod, h, Nat.add_mod]
        omega 
      have h4 : 25 ∣ ( (2 ^ (6 + 100 * k) * 2 ^ 100) + (6 + 100 * k + 100) ^ 2 ) := by
        have eq1 : ( (2 ^ (6 + 100 * k) * 2 ^ 100) + (6 + 100 * k + 100) ^ 2 ) % 25 = 0 := by
          have eq2 : (2 ^ (6 + 100 * k) ) % 25 = ( 14 : ℕ) := by
            have h7 : ∀ (k_0 : ℕ), (2 ^ (6 + 100 * k_0) ) % 25 = 14 := by 
              intro k_0
              induction k_0 with
              | zero =>
                norm_num 
              | succ k_0 ih =>
                simp [Nat.pow_add, Nat.pow_mul, Nat.pow_succ, Nat.mul_mod] at ih ⊢
                all_goals omega
            exact h7 k 
          have eq3 : (6 + 100 * k + 100 : ℕ) % 25 = 6 := by 
            omega 
          have eq4 : ( (2 ^ (6 + 100 * k) * 2 ^ 100) + (6 + 100 * k + 100) ^ 2 ) % 25 = 0 := by
            simp [Nat.add_mod, Nat.mul_mod, eq2, eq3, pow_two]
          exact eq4 
        omega 
      omega 
  have h2 : ∃ k : ℕ, 6 + 100 * k > N := by 
    use (N + 1) 
    omega 
  rcases h2 with ⟨k, hk⟩ 
  use 6 + 100 * k 
  constructor 
  · linarith 
  · exact h1 k