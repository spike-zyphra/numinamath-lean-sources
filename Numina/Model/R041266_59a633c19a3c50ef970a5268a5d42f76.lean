import Mathlib

theorem number_theory_257025 (n : ℕ) (hn : n > 0) :
    5 ∣ 1^n + 2^n + 3^n + 4^n ↔ ¬4 ∣ n := by
  constructor
  · -- Forward direction: If 5 divides 1^n + 2^n + 3^n + 4^n, then ¬4 divides n
    intro h
    by_contra h1
    -- Assume 4 divides n, we need to show contradiction in 5 dividing the sum
    have h2 : 4 ∣ n := h1
    rcases h2 with ⟨k, hk⟩
    rw [show n = 4 * k by omega] at h
    have h3 : (1 ^ (4 * k) + 2 ^ (4 * k) + 3 ^ (4 * k) + 4 ^ (4 * k) : ℕ) % 5 = 4 := by
      have h11 : ∀ k : ℕ, (1 ^ (4 * k) + 2 ^ (4 * k) + 3 ^ (4 * k) + 4 ^ (4 * k) : ℕ) % 5 = 4 := by
        intro k
        induction k with
        | zero => 
          simp
        | succ k ih =>
          simp [Nat.pow_add, Nat.pow_mul, Nat.pow_mul] at ih ⊢
          all_goals omega
      specialize h11 k
      simpa using h11
    have h4 : 5 ∣ (1 ^ (4 * k) + 2 ^ (4 * k) + 3 ^ (4 * k) + 4 ^ (4 * k) : ℕ) := by
      simpa using h
    omega
  · -- Backward direction: If ¬4 divides n, then 5 divides 1^n + 2^n + 3^n + 4^n
    intro h
    have h6 : n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
      omega
    rcases h6 with (h | h | h)
    · -- Case n % 4 = 1
      have h11 : (1 ^ n + 2 ^ n + 3 ^ n + 4 ^ n) % 5 = 0 := by
        have h111 : ∀ k : ℕ, (1 ^ (4 * k + 1) + 2 ^ (4 * k + 1) + 3 ^ (4 * k + 1) + 4 ^ (4 * k + 1) : ℕ) % 5 = 0 := by
          intro k
          induction k with
          | zero => 
            norm_num
          | succ k ih =>
            simp [Nat.pow_add, Nat.pow_mul, Nat.pow_mul] at ih ⊢
            all_goals omega
        have h112 : ∃ k : ℕ, n = 4 * k + 1 := by 
          refine' ⟨n / 4, by omega⟩
        rcases h112 with ⟨k, h113⟩
        rw [h113] at *
        specialize h111 k
        simpa using h111
      omega
    · -- Case n % 4 = 2
      have h11 : (1 ^ n + 2 ^ n + 3 ^ n + 4 ^ n) % 5 = 0 := by
        have h111 : ∀ k : ℕ, (1 ^ (4 * k + 2) + 2 ^ (4 * k + 2) + 3 ^ (4 * k + 2) + 4 ^ (4 * k + 2) : ℕ) % 5 = 0 := by
          intro k
          induction k with
          | zero => 
            norm_num
          | succ k ih =>
            simp [Nat.pow_add, Nat.pow_mul, Nat.pow_mul] at ih ⊢
            all_goals omega
        have h112 : ∃ k : ℕ, n = 4 * k + 2 := by 
          refine' ⟨n / 4, by omega⟩
        rcases h112 with ⟨k, h113⟩
        rw [h113] at *
        specialize h111 k
        simpa using h111
      omega
    · -- Case n % 4 = 3
      have h11 : (1 ^ n + 2 ^ n + 3 ^ n + 4 ^ n) % 5 = 0 := by
        have h111 : ∀ k : ℕ, (1 ^ (4 * k + 3) + 2 ^ (4 * k + 3) + 3 ^ (4 * k + 3) + 4 ^ (4 * k + 3) : ℕ) % 5 = 0 := by
          intro k
          induction k with
          | zero => 
            norm_num
          | succ k ih =>
            simp [Nat.pow_add, Nat.pow_mul, Nat.pow_mul] at ih ⊢
            all_goals omega
        have h112 : ∃ k : ℕ, n = 4 * k + 3 := by 
          refine' ⟨n / 4, by omega⟩
        rcases h112 with ⟨k, h113⟩
        rw [h113] at *
        specialize h111 k
        simpa using h111
      omega