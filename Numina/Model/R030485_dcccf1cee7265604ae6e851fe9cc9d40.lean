import Mathlib
theorem algebra_607329 (x : ℕ → ℝ) (y : ℕ → ℝ)
(h0 : x 0 = 0) (h1 : x 1 = 1) (h2 : ∀ n, x (n + 2) = 3 * x (n + 1) - 2 * x n) (h3 : ∀ n, y n = x n ^ 2 + 2 ^ (n + 2)) :
∀ n > 0, ∃ m : ℕ, m ^ 2 = y n ∧ Odd m:= by
  intro n hn
  have h4 : ∀ (n : ℕ), x n = (2 : ℝ) ^ n - 1 := by
    intro n 
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      rw [h0]
      norm_num
    | succ n =>
      cases n with
      | zero =>
        rw [h1]
        norm_num
      | succ n =>
        have eq1 := ih (n) (by linarith)
        have eq2 := ih (n + 1) (by linarith)
        simp [h2, eq1, eq2]
        ring_nf
  have h5 : y n = ((2 : ℝ) ^ n + 1) ^ 2 := by
    have h6 : y n = x n ^ 2 + (2 : ℝ) ^ (n + 2 : ℕ) := by
      specialize h3 n
      simpa using h3
    rw [h6]
    have h7 : x n = (2 : ℝ) ^ n - 1 := h4 n
    rw [h7]
    ring_nf
  use (2 ^ n + 1 : ℕ)
  constructor
  · -- Show m^2 = y n
    have h8 : ((2 ^ n + 1 : ℕ) : ℝ) ^ 2 = y n := by
      rw [h5]
      simp
    norm_num at h8 ⊢
    nlinarith
  · -- Show m is odd
    have h10 : Odd (2 ^ n + 1 : ℕ) := by
      have h11 : (2 ^ n + 1 : ℕ) % 2 = 1 := by
        have h11 : n > 0 := hn
        have h12 : n ≥ 1 := by omega
        have h13 : (2 ^ n : ℕ) % 2 = 0 := by
          have h14 : ∀ k : ℕ, (2 ^ (k + 1) : ℕ) % 2 = 0 := by
            intro k
            induction k with
            | zero => norm_num
            | succ k ih =>
              simp [Nat.pow_succ, Nat.mul_mod] at ih ⊢
          have h15 : n ≥ 1 := by omega
          have h16 : ∃ k, n = k + 1 := by
            use n - 1
            omega
          rcases h16 with ⟨k, hk⟩
          rw [hk]
          specialize h14 k
          simpa using h14
        omega
      exact Nat.odd_iff.mpr h11
    simpa using h10