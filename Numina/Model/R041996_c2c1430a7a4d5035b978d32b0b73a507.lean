import Mathlib

theorem number_theory_285814 (n : ℕ) : 5 ∣ 2^n - 1 ∨ 5 ∣ 2^n + 1 ∨ 5 ∣ 2^(2*n) + 1 := by 
  have h1 : (2 : ℕ) ^ n % 5 = 1 ∨ (2 : ℕ) ^ n % 5 = 2 ∨ (2 : ℕ) ^ n % 5 = 3 ∨ (2 : ℕ) ^ n % 5 = 4 := by
    have h2 : ∀ n : ℕ, (2 : ℕ) ^ n % 5 = 1 ∨ (2 : ℕ) ^ n % 5 = 2 ∨ (2 : ℕ) ^ n % 5 = 3 ∨ (2 : ℕ) ^ n % 5 = 4 := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        have h2n1 : (2 : ℕ) ^ (n + 1) % 5 = (2 ^ n * 2) % 5 := by
          ring_nf
        rw [h2n1]
        rcases ih with (h | h | h | h)
        · simp [Nat.mul_mod, h]
        · simp [Nat.mul_mod, h]
        · simp [Nat.mul_mod, h]
        · simp [Nat.mul_mod, h]
    specialize h2 n
    simpa using h2
  rcases h1 with (h1 | h1 | h1 | h1)
  · -- case where $2^n \equiv 1 \pmod{5}$, so $5 \mid 2^n - 1$.
    have h2 : (2^n - 1 : ℕ) % 5 = 0 := by
      omega
    omega
  · -- case where $2^n \equiv 2 \pmod{5}$, then $2^{2n} + 1 \equiv (2^n)^2 +1 \equiv 2^2 +1 \equiv 4+1 \equiv 0 \pmod{5}$.
    have h3 : (2^(2 * n) + 1 : ℕ) % 5 = 0 := by
      have h4 : (2^(2 * n)) % 5 = 4 := by
        have h5 : (2^n) % 5 = 2 := h1
        have h6 : (2^(2 * n)) % 5 = ((2^n) ^ 2) % 5 := by
          ring_nf
        rw [h6]
        simp [Nat.pow_mod, h5]
      omega
    omega
  · -- case where $2^n \equiv 3 \pmod{5}$, then $2^{2n} + 1 \equiv (2^n)^2 +1 \equiv 3^2+1 \equiv 9+1 \equiv 10 \equiv 0 \pmod{5}$.
    have h3 : (2^(2 * n) + 1 : ℕ) % 5 = 0 := by
      have h4 : (2^(2 * n)) % 5 = 4 := by
        have h5 : (2^n) % 5 = 3 := h1
        have h6 : (2^(2 * n)) % 5 = ((2^n) ^ 2) % 5 := by
          ring_nf
        rw [h6]
        simp [Nat.pow_mod, h5]
      omega
    omega
  · -- case where $2^n \equiv 4 \pmod{5}$, then $5 \mid 2^n + 1$.
    have h2 : (2^n + 1 : ℕ) % 5 = 0 := by
      omega
    omega