import Mathlib

theorem number_theory_264854 (n : ℕ) (hn : n > 0) :
    ¬ 5 ∣ (1^n + 2^n + 3^n + 4^n + 5^n + 6^n + 7^n + 8^n) := by
  have h1 : n ≥ 1 := by linarith
  by_contra h
  have h2 : (1^n + 2^n + 3^n + 4^n + 5^n + 6^n + 7^n + 8^n) % 5 = 0 := by
    omega
  have h3 : (1^n + 2^n + 3^n + 4^n + 5^n + 6^n + 7^n + 8^n) % 5 = ( (1^n) % 5 + (2^n) % 5 + (3^n) % 5 + (4^n) % 5 + (5^n) % 5 + (6^n) % 5 + (7^n) % 5 + (8^n) % 5 ) % 5 := by
    simp [Nat.add_mod]
    <;> ring_nf <;> omega
  rw [h3] at h2
  have h4 : (1^n) % 5 = 1 := by
    have h : ∀ n : ℕ, n ≥ 1 → (1^n : ℕ) % 5 = 1 := by
      intro n hn
      induction n with
      | zero => linarith
      | succ n ih =>
        cases n with
        | zero => simp [pow_succ]
        | succ n =>
          simp [pow_succ] at ih ⊢
          all_goals omega
    apply h n h1
  have h8 : (5^n) % 5 = 0 := by
    have h5 : ∀ n : ℕ, n ≥ 1 → (5^n) % 5 = 0 := by
      intro n hn
      induction n with
      | zero => linarith
      | succ n ih =>
        cases n with
        | zero => simp [pow_succ]
        | succ n =>
          simp [pow_succ] at ih ⊢
          all_goals omega
    apply h5 n h1
  have h9 : (6^n) % 5 = (1^n) % 5 := by
    have h : ∀ n : ℕ, n ≥ 1 → (6^n) % 5 = (1^n) % 5 := by
      intro n hn
      induction n with
      | zero => linarith
      | succ n ih =>
        cases n with
        | zero => simp [pow_succ]
        | succ n =>
          simp [pow_succ] at ih ⊢
          all_goals omega
    apply h n h1
  have h10 : (7^n) % 5 = (2^n) % 5 := by
    have h : ∀ n : ℕ, n ≥ 1 → (7^n) % 5 = (2^n) % 5 := by
      intro n hn
      induction n with
      | zero => linarith
      | succ n ih =>
        cases n with
        | zero => simp [pow_succ]
        | succ n =>
          simp [pow_succ] at ih ⊢
          all_goals omega
    apply h n h1
  have h11 : (8^n) % 5 = (3^n) % 5 := by
    have h : ∀ n : ℕ, n ≥ 1 → (8^n) % 5 = (3^n) % 5 := by
      intro n hn
      induction n with
      | zero => linarith
      | succ n ih =>
        cases n with
        | zero => simp [pow_succ]
        | succ n =>
          simp [pow_succ] at ih ⊢
          all_goals omega
    apply h n h1
  simp [h4, h8, h9, h10, h11] at h2
  have h12 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases h12 with (h12 | h12 | h12 | h12)
  · -- n ≡ 0
    have h13 : n % 4 = 0 := h12
    have h2n : (2^n) % 5 = 1 := by
      have h20 : ∀ k : ℕ, (2^(4*k)) % 5 = 1 := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          simp [pow_succ, pow_mul] at ih ⊢
          all_goals omega
      have h21 : n = 4 * (n / 4) := by
        omega
      rw [h21]
      specialize h20 (n / 4)
      simpa using h20
    have h3n : (3^n) % 5 = 1 := by
      have h30 : ∀ k : ℕ, (3^(4*k)) % 5 = 1 := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          simp [pow_succ, pow_mul] at ih ⊢
          all_goals omega
      have h31 : n = 4 * (n / 4) := by
        omega
      rw [h31]
      specialize h30 (n / 4)
      simpa using h30
    have h4n : (4^n) % 5 = 1 := by
      have h40 : ∀ k : ℕ, (4^(4*k)) % 5 = 1 := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          simp [pow_succ, pow_mul] at ih ⊢
          all_goals omega
      have h41 : n = 4 * (n / 4) := by
        omega
      rw [h41]
      specialize h40 (n / 4)
      simpa using h40
    simp [h2n, h3n, h4n] at h2
    all_goals omega
  · -- n ≡ 1
    have h14 : n % 4 = 1 := h12
    have h2n : (2^n) % 5 = 2 := by
      have h20 : ∀ k : ℕ, (2^(4*k+1)) % 5 = 2 := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          simp [pow_succ, pow_mul] at ih ⊢
          all_goals omega
      have h21 : n = 4 * (n / 4) + 1 := by
        omega
      rw [h21]
      specialize h20 (n / 4)
      simpa using h20
    have h3n : (3^n) % 5 = 3 := by
      have h30 : ∀ k : ℕ, (3^(4*k+1)) % 5 = 3 := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          simp [pow_succ, pow_mul] at ih ⊢
          all_goals omega
      have h31 : n = 4 * (n / 4) + 1 := by
        omega
      rw [h31]
      specialize h30 (n / 4)
      simpa using h30
    have h4n : (4^n) % 5 = 4 := by
      have h40 : ∀ k : ℕ, (4^(4*k+1)) % 5 = 4 := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          simp [pow_succ, pow_mul] at ih ⊢
          all_goals omega
      have h41 : n = 4 * (n / 4) + 1 := by
        omega
      rw [h41]
      specialize h40 (n / 4)
      simpa using h40
    simp [h2n, h3n, h4n] at h2
    all_goals omega
  · -- n ≡ 2
    have h15 : n % 4 = 2 := h12
    have h2n : (2^n) % 5 = 4 := by
      have h20 : ∀ k : ℕ, (2^(4*k+2)) % 5 = 4 := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          simp [pow_succ, pow_mul] at ih ⊢
          all_goals omega
      have h21 : n = 4 * (n / 4) + 2 := by
        omega
      rw [h21]
      specialize h20 (n / 4)
      simpa using h20
    have h3n : (3^n) % 5 = 4 := by
      have h30 : ∀ k : ℕ, (3^(4*k+2)) % 5 = 4 := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          simp [pow_succ, pow_mul] at ih ⊢
          all_goals omega
      have h31 : n = 4 * (n / 4) + 2 := by
        omega
      rw [h31]
      specialize h30 (n / 4)
      simpa using h30
    have h4n : (4^n) % 5 = 1 := by
      have h40 : ∀ k : ℕ, (4^(4*k+2)) % 5 = 1 := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          simp [pow_succ, pow_mul] at ih ⊢
          all_goals omega
      have h41 : n = 4 * (n / 4) + 2 := by
        omega
      rw [h41]
      specialize h40 (n / 4)
      simpa using h40
    simp [h2n, h3n, h4n] at h2
    all_goals omega
  · -- n ≡ 3
    have h16 : n % 4 = 3 := h12
    have h2n : (2^n) % 5 = 3 := by
      have h20 : ∀ k : ℕ, (2^(4*k+3)) % 5 = 3 := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          simp [pow_succ, pow_mul] at ih ⊢
          all_goals omega
      have h21 : n = 4 * (n / 4) + 3 := by
        omega
      rw [h21]
      specialize h20 (n / 4)
      simpa using h20
    have h3n : (3^n) % 5 = 2 := by
      have h30 : ∀ k : ℕ, (3^(4*k+3)) % 5 = 2 := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          simp [pow_succ, pow_mul] at ih ⊢
          all_goals omega
      have h31 : n = 4 * (n / 4) + 3 := by
        omega
      rw [h31]
      specialize h30 (n / 4)
      simpa using h30
    have h4n : (4^n) % 5 = 4 := by
      have h40 : ∀ k : ℕ, (4^(4*k+3)) % 5 = 4 := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          simp [pow_succ, pow_mul] at ih ⊢
          all_goals omega
      have h41 : n = 4 * (n / 4) + 3 := by
        omega
      rw [h41]
      specialize h40 (n / 4)
      simpa using h40
    simp [h2n, h3n, h4n] at h2
    all_goals omega