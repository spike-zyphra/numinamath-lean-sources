import Mathlib

theorem algebra_115070 (n : ℕ) :
    (5^(2*n) + 5^(n+2) + 114) / (4 * 5^n + 24) = (5^n + 19) / 4 ∧
    ∃ m : ℕ, (5^(2*n) + 5^(n+2) + 114) / (4 * 5^n + 24) = m := by

  constructor
  · -- Show that (5^(2*n) + 5^(n+2) + 114) / (4 * 5^n + 24) = (5^n + 19) / 4
    have h1 : 4 * (5 ^ (2 * n) + 5 ^ (n + 2) + 114 : ℕ) = (4 * 5 ^ n + 24 : ℕ) * (5 ^ n + 19 : ℕ) := by
      have h2 : 5 ^ (n + 2) = 25 * 5 ^ n := by
        have h3 : 5 ^ (n + 2) = 5 ^ n * 5 ^ 2 := by ring
        rw [h3]
        ring_nf
      have h4 : 5 ^ (2 * n) = (5 ^ n) ^ 2 := by 
        ring_nf
      rw [h2, h4]
      ring_nf

    have h11 : 4 ∣ (5 ^ n + 19 : ℕ) := by
      have h12 : (5 ^ n + 19 : ℕ) % 4 = 0 := by
        have h1 : ∀ (n : ℕ), (5 ^ n + 19 : ℕ) % 4 = 0 := by
          intro n
          induction n with 
          | zero => 
            norm_num
          | succ n ih =>
            simp [Nat.pow_succ, Nat.add_mod, Nat.mul_mod] at ih ⊢
            all_goals omega
        specialize h1 n
        simpa using h1
      have h13 : 4 ∣ (5 ^ n + 19 : ℕ) := by 
        omega
      exact h13

    rcases h11 with ⟨k, hk⟩

    have h20 : (5 ^ (2 * n) + 5 ^ (n + 2) + 114 : ℕ) = (4 * 5 ^ n + 24 : ℕ) * k := by 
      nlinarith [h1, hk]

    have h21 : (5 ^ (2 * n) + 5 ^ (n + 2) + 114 : ℕ) / (4 * 5 ^ n + 24 : ℕ) = k := by 
      rw [h20]
      simp

    have h22 : k = (5 ^ n + 19 : ℕ) / 4 := by 
      omega

    rw [h21, h22]

  · -- Show that A is a natural number. 
    refine' ⟨(5 ^ (2 * n) + 5 ^ (n + 2) + 114) / (4 * 5 ^ n + 24), rfl⟩