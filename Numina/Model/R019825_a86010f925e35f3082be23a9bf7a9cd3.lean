import Mathlib

theorem number_theory_111703 {n : ℕ} (hn : n % 10 = 4 ∧ n % 7 = 5) :
    14 ∣ n + 2 ∧ 2014 ∣ 2013 ^ n - 1 := by 
  rcases hn with ⟨h10, h7⟩
  have h14 : 14 ∣ n + 2 := by
    omega
  have h2014 : 2014 ∣ 2013 ^ n - 1 := by
    have h1 : n % 2 = 0 := by
      omega
    have h3 : (2013 : ℕ) ^ n % 2 = 1 := by
      have h4 : ∀ k : ℕ, (2013 : ℕ) ^ k % 2 = 1 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
          all_goals omega
      specialize h4 n
      simpa using h4
    -- modulo 19: 2013 \equiv -1 \pmod{19}
    have h5 : (2013 : ℕ) ^ n % 19 = 1 := by
      have h1' : n % 2 = 0 := h1
      have h4 : ∀ k : ℕ, (2013 : ℕ) ^ (2 * k) % 19 = 1 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          simp [pow_add, pow_mul] at ih ⊢
          omega
      have : ∃ k : ℕ, n = 2 * k := by
        refine' ⟨n / 2, by omega⟩
      rcases this with ⟨k, hk⟩
      rw [show n = 2 * k by omega]
      specialize h4 k
      simpa using h4
    -- modulo 53: 2013 \equiv -1 \pmod{53}
    have h6 : (2013 : ℕ) ^ n % 53 = 1 := by
      have h1' : n % 2 = 0 := h1
      have h7 : ∀ k : ℕ, (2013 : ℕ) ^ (2 * k) % 53 = 1 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          simp [pow_add, pow_mul] at ih ⊢
          omega
      have : ∃ k : ℕ, n = 2 * k := by
        refine' ⟨n / 2, by omega⟩
      rcases this with ⟨k, hk⟩
      rw [show n = 2 * k by omega]
      specialize h7 k
      simpa using h7
    omega
  constructor
  · exact h14
  · exact h2014