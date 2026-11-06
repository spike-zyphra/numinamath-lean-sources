import Mathlib

theorem number_theory_243364 (n : ℕ) :
    (Odd n → 8 ∣ (7^n + 1)) ∧ (Even n → ¬8 ∣ (7^n + 1)) := by
  constructor 
  · -- Prove that for any odd n, $8 \mid (7^n + 1)$.
    intro h
    have h1 : n % 2 = 1 := by 
      obtain ⟨m, hm⟩ := h 
      omega 
    have h3 : 7^n % 8 = 7 := by
      have h4 : ∀ k : ℕ, 7^(2*k+1) % 8 = 7 := by 
        intro k 
        induction k with 
        | zero =>
          norm_num 
        | succ k ih =>
          have h5 : (2*(k+1)+1) = (2*k+1+2) := by ring 
          rw [h5]
          norm_num [Nat.pow_add, Nat.mul_mod, Nat.add_mod] at ih ⊢ 
          all_goals omega 
      have h5 : ∃ k : ℕ, n = 2*k+1 := by
        have : n % 2 = 1 := h1
        have : n % 2 = 1 := h1
        refine' ⟨(n - 1) / 2, by omega⟩ 
      rcases h5 with ⟨k, hk⟩
      rw [show n = 2*k+1 by exact_mod_cast hk] 
      exact h4 k
    have h0 : (7^n + 1) % 8 = 0 := by
      omega
    exact Nat.dvd_of_mod_eq_zero h0 
  · -- Prove that for any even n, $8 \nmid (7^n + 1)$.
    intro h
    have h1 : n % 2 = 0 := by 
      obtain ⟨m, hm⟩ := h 
      omega 
    intro h2 
    have h3 : (7^n + 1) % 8 = 0 := by 
      omega 
    -- We know that for even n, 7^n ≡ 1 (mod 8).
    have h4 : ∀ n : ℕ, (n % 2 = 0) → 7^n % 8 = 1 := by 
      intro n hn 
      have h7 : ∀ k : ℕ, 7^(2*k) % 8 = 1 := by 
        intro k 
        induction k with 
        | zero => 
          simp 
        | succ k ih =>
          have h6 : (2*(k+1)) = (2*k + 2) := by ring 
          rw [h6]
          norm_num [Nat.pow_add, Nat.mul_mod, Nat.add_mod] at ih ⊢ 
          all_goals omega 
      have h7' : ∃ k : ℕ, n = 2*k := by
        have : n % 2 = 0 := hn 
        refine' ⟨n / 2, by omega⟩ 
      rcases h7' with ⟨k, hk⟩ 
      rw [show n = 2*k by exact_mod_cast hk]
      exact h7 k
    have h5 : 7^n % 8 = 1 := h4 n h1 
    have h6 : (7^n + 1) % 8 = 2 := by 
      omega 
    omega 
    all_goals omega 
    all_goals omega