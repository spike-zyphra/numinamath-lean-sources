import Mathlib
theorem number_theory_31249 (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (hne : ¬(4 ∣ m)) (h : 3 * m * k = (m + 3) ^ n + 1) : Odd k:= by
  have h1 : m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by
    omega
  rcases h1 with (h1 | h1 | h1)
  · -- m ≡ 1 (mod 4)
    have h2 : (m + 3) % 4 = 0 := by
      omega
    have h4 : ((m + 3) ^ n) % 4 = 0 := by
      have h4 : ∀ (n : ℕ), n > 0 → (m + 3) ^ n % 4 = 0 := by
        intro n hn
        induction n with
        | zero =>
          omega
        | succ n ih =>
          cases n with
          | zero =>
            simp [h2]
          | succ n =>
            simp [Nat.pow_succ, Nat.mul_mod, h2] at ih ⊢
            all_goals omega
      specialize h4 n (by omega)
      simpa using h4
    have h5 : ((m + 3) ^ n + 1) % 4 = 1 := by
      omega
    have h6 : (3 * m * k) % 4 = 1 := by
      omega
    have h7 : k % 2 = 1 := by
      have h11 : (3 * m * k) % 4 = (3 * (m % 4) * (k % 4)) % 4 := by
        simp [Nat.mul_mod]
      rw [h11] at h6
      rw [show m % 4 = 1 by omega] at h6
      have h13 : k % 4 = 1 ∨ k % 4 = 3 := by
        omega
      omega
    exact Nat.odd_iff.mpr h7
  · -- m ≡ 2 (mod 4)
    have h2 : (m + 3) % 4 = 1 := by
      omega
    have h3 : ((m + 3) ^ n) % 4 = 1 := by
      have h4 : ∀ (n : ℕ), ((m + 3) ^ n) % 4 = 1 := by
        intro n
        induction n with
        | zero =>
          simp
        | succ n ih =>
          simp [Nat.pow_succ, Nat.mul_mod, h2] at ih ⊢
          all_goals omega
      specialize h4 n
      simpa using h4
    have h5 : ((m + 3) ^ n + 1) % 4 = 2 := by
      omega
    have h6 : (3 * m * k) % 4 = 2 := by
      omega
    have h7 : k % 2 = 1 := by
      have h11 : (3 * m * k) % 4 = (3 * (m % 4) * (k % 4)) % 4 := by
        simp [Nat.mul_mod]
      rw [h11] at h6
      rw [show m % 4 = 2 by omega] at h6
      have h13 : k % 4 = 1 ∨ k % 4 = 3 := by
        omega
      omega
    exact Nat.odd_iff.mpr h7
  · -- m ≡ 3 (mod 4)
    have h2 : (m + 3) % 4 = 2 := by
      omega
    have h5 : ((m + 3) ^ n + 1) % 4 = 1 ∨ ((m + 3) ^ n + 1) % 4 = 3 := by
      have h4 : ((m + 3) ^ n) % 4 = 0 ∨ ((m + 3) ^ n) % 4 = 2 := by
        have h22 : ∀ (n : ℕ), n > 0 → ((m + 3) ^ n) % 4 = 0 ∨ ((m + 3) ^ n) % 4 = 2 := by
          intro n hn
          induction n with
          | zero =>
            omega
          | succ n ih =>
            cases n with
            | zero =>
              simp [h2]
            | succ n =>
              simp [Nat.pow_succ, Nat.mul_mod, h2] at ih ⊢
              all_goals omega
        specialize h22 n (by omega)
        simpa using h22
      rcases h4 with (h4 | h4)
      · 
        omega
      · 
        omega
    have h6 : (3 * m * k) % 4 = 1 ∨ (3 * m * k) % 4 = 3 := by
      omega
    have h7 : k % 2 = 1 := by
      have h11 : (3 * m * k) % 4 = k % 4 := by
        simp [Nat.mul_mod, h1]
      rw [h11] at h6
      have h13 : k % 4 = 1 ∨ k % 4 = 3 := by
        omega
      omega
    exact Nat.odd_iff.mpr h7