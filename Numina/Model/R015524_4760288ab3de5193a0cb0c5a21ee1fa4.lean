import Mathlib

theorem number_theory_270128 {n : ℕ} (hn : Odd n) :
    n^2 ≡ 1 [MOD 8] ∧ ∃ k, n^2 / 8 = k * (k + 1) / 2 := by

  have h1 : n % 2 = 1 := by
    obtain ⟨k, hk⟩ := hn
    omega

  have h2 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
    have h1' : n % 2 = 1 := h1
    omega

  have h3 : n ^ 2 % 8 = 1 := by
    rcases h2 with (h | h | h | h) <;> simp [Nat.pow_mod, h, Nat.mul_mod]

  have h4 : n % 2 = 1 := h1

  have h5 : ∃ k, n^2 / 8 = k * (k + 1) / 2 := by
    obtain ⟨m, hm⟩ := hn
    use m
    have h7 : n = 2 * m + 1 := by linarith
    rw [h7]
    ring_nf
    <;> omega

  constructor
  · -- Proof that n^2 ≡ 1 [MOD 8]
    simp [Nat.ModEq, h3]
  · -- Proof of existence of k
    exact h5