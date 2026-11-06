import Mathlib

theorem number_theory_14111 (n : ℕ) (hn : n > 0) (a : ℕ)
    (ha : a * (3^(2*n) + 4) ≡ 1 [MOD 9]) : a ≡ 7 [MOD 9] := by
  have h1 : (3 : ℕ) ^ (2 * n) % 9 = 0 := by
    have h2 : ∀ k : ℕ, (3 : ℕ) ^ (2 * (k + 1)) % 9 = 0 := by 
      intro k
      induction k with 
      | zero =>
        norm_num
      | succ k ih =>
        simp [Nat.pow_succ, Nat.pow_mul, Nat.pow_add] at ih ⊢
        all_goals omega 
    have h3 : 2 * (n - 1 + 1) = 2 * n := by
      cases n with
      | zero => linarith 
      | succ n =>
        simp [Nat.add_assoc, Nat.mul_add, Nat.add_mul]
        <;> ring_nf 
        <;> omega 
    specialize h2 (n - 1)
    have h4 : (3 ^ (2 * (n - 1 + 1)) ) % 9 = 0 := h2 
    rw [h3] at h4 
    exact h4 
  have h2 : (3 ^ (2 * n) + 4) % 9 = 4 := by 
    have h1' : (3 ^ (2 * n) : ℕ) % 9 = 0 := h1 
    omega 
  simp [Nat.ModEq] at ha ⊢
  have h3 : a * (3 ^ (2 * n) + 4) % 9 = 1 := by
    simpa using ha 
  have h4 : (3 ^ (2 * n) + 4) % 9 = 4 := h2 
  simp [Nat.mul_mod, h4] at h3 
  all_goals omega